/*
 * Given an H.222 transport stream (TS) file, extract elementary stream
 * data therefrom (i.e., extract the ES from the PES packets within the
 * TS).
 *
 * ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is the MPEG TS, PS and ES tools.
 *
 * The Initial Developer of the Original Code is Amino Communications Ltd.
 * Portions created by the Initial Developer are Copyright (C) 2008
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Amino Communications Ltd, Swavesey, Cambridge UK
 *
 * ***** END LICENSE BLOCK *****
 */

#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <fcntl.h>
#ifdef _WIN32
#include <stddef.h>
#else // _WIN32
#include <unistd.h>
#endif // _WIN32

#include "compat.h"
#include "ts_fns.h"
#include "misc_fns.h"
#include "printing_fns.h"
#include "pidint_fns.h"
#include "es_fns.h"
#include "pes_fns.h"
#include "version.h"

// A three-way choice for what to output by PID
enum pid_extract
{
  EXTRACT_UNDEFINED,
  EXTRACT_VIDEO,  // Output the first "named" video stream
  EXTRACT_AUDIO,  // Ditto for audio
  EXTRACT_PID,    // Output an explicit PID
};
typedef enum pid_extract EXTRACT;


/*
 * Find the first candidate PES start code within b[from..len).
 *
 * A candidate is '00 00 01' followed by a byte >= 0xB8 (MPEG-1 PS
 * pack/system/PSM ids 0xB9-0xBF, or H.222.0 stream ids 0xC0-0xFF).
 * Stream ids 0xC0-0xFF must carry the H.222.0 marker bits in the
 * octet after the 16-bit length field; a mid-NAL '00 00 01 xx'
 * pattern usually fails this and is skipped. A candidate near the
 * end of the buffer (marker octet not visible) is accepted and
 * resolved when the header completes in the next packet.
 *
 * Returns the offset of the start code, or -1 if none was found.
 */
static int find_pes_start(const byte *b, int len, int from)
{
  int  i;

  for (i = from; i + 3 < len; i++)
  {
    if (b[i] == 0 && b[i+1] == 0 && b[i+2] == 1 && b[i+3] >= 0xB8)
    {
      if (b[i+3] >= 0xC0 && i + 6 < len && (b[i+6] & 0xC0) != 0x80)
        continue;
      return i;
    }
  }
  return -1;
}

/*
 * Write a chunk of ES data, dying if the write fails.
 *
 * Returns 0 on success, 1 on error.
 */
static int write_es_bytes(FILE         *output,
                          const byte   *data,
                          int           len)
{
  if (len > 0)
  {
    // Windows doesn't seem to like writing 0 bytes, so be careful...
    size_t  written = fwrite(data,len,1,output);
    if (written != 1)
    {
      fprint_err("### Error writing TS packet - units written = %d\n",
                 (int)written);
      return 1;
    }
  }
  return 0;
}

/*
 * Given a start code at buf[f], parse the PES header.
 *
 * On success sets *pos (the ES offset within buf) and *unit_left (the
 * unit's ES size, 0 when unknown) and returns 0. If the header does
 * not complete within buf, the staged state (pend/pend_len/hdr_total)
 * is updated for the next packet and 1 is returned.
 */
static int parse_pes_header(byte      *buf,
                            int         blen,
                            int         f,
                            byte       *pend,
                            int        *pend_len,
                            int        *hdr_total,
                            int        *pos,
                            int        *unit_left,
                            int         verbose)
{
  int  declared;
  int  hd;

  if (buf[f+3] < 0xC0)
  {
    // MPEG-1 PS (pack/system/PSM ids 0xB9-0xBF): no reliable 16-bit
    // PES length exists, so just drop the header.
    int  off = calc_mpeg1_pes_offset(buf + f,blen - f);

    *pos = f + off;
    if (*pos > blen)
      *pos = blen;   // legacy approximation: assume the header fits
    *unit_left = 0;
    return 0;
  }

  // H.222.0: the ES data starts PES_header_data_length bytes after
  // the 16-bit length field (9 bytes from the start code). All field
  // offsets are anchored on the three-byte view '00 00 01', which is
  // the same whether the start code was written with three or four
  // zero bytes. PES_packet_length (when non-zero) counts octets from
  // after the length field, so the PES carries declared - (3 + hd)
  // ES octets.
  if (f + 8 >= blen)
  {
    // The header doesn't complete in this buffer: stage it.
    if (verbose)
      fprint_msg("PES header spills into next packet\n");
    memcpy(pend,buf + f,blen - f);
    *pend_len = blen - f;
    *hdr_total = 0;
    return 1;
  }

  declared = (buf[f+4] << 8) | buf[f+5];
  hd = buf[f+8];
  *pos = f + 9 + hd;
  *unit_left = 0;
  if (declared > 0)
  {
    *unit_left = declared - (3 + hd);
    if (*unit_left < 0)
      *unit_left = 0;
    if (verbose)
      fprint_msg("PES packet length %d (%d ES bytes)\n",
                 declared,*unit_left);
  }

  if (*pos > blen)
  {
    // The header fits, but the ES starts in the next buffer: stage
    // the (complete) header bytes.
    memcpy(pend,buf + f,blen - f);
    *pend_len = blen - f;
    *hdr_total = 9 + hd;
    return 1;
  }
  return 0;
}

/*
 * Write the current unit's ES from buf[pos] onward. When a
 * declared-length unit ends inside the buffer, the next unit starts
 * right after it: scan for and parse that start (this is only ever
 * called for PUSI packets, the only place a new unit may start).
 *
 * Returns 0 on success (state updated), 1 on a write error.
 */
static int emit_unit_es(byte      *buf,
                        int         blen,
                        int        *pos,
                        byte       *pend,
                        int        *pend_len,
                        int        *hdr_total,
                        int        *unit_left,
                        FILE       *output)
{
  int  f;

  for (;;)
  {
    int  avail = blen - *pos;
    int  w = avail;

    if (*unit_left > 0 && w > *unit_left)
      w = *unit_left;
    if (write_es_bytes(output,buf + *pos,w))
      return 1;
    *pos += w;

    if (*unit_left == 0)
      break;             // unknown-length unit carries on
    *unit_left -= w;
    if (*unit_left > 0)
      break;             // unit continues in later packets

    // A declared-length unit ended right here.
    if (*pos >= blen)
      break;
    f = find_pes_start(buf,blen,*pos);
    if (f < 0)
    {
      // No start code visible: the next unit's start code may
      // straddle into the next packet (at most 3 bytes here). Hold
      // a start-code prefix; preserve anything else (malformed).
      int  rest = blen - *pos;
      int  prefix = 0;

      if (rest == 3 && buf[*pos] == 0 && buf[*pos+1] == 0 &&
          buf[*pos+2] == 1)
        prefix = 3;
      else
        while (prefix < rest && buf[*pos + prefix] == 0)
          prefix ++;
      if (prefix > 0 && prefix == rest)
      {
        memcpy(pend,buf + *pos,rest);
        *pend_len = rest;
        *hdr_total = 0;
      }
      else if (rest > 0)
      {
        if (write_es_bytes(output,buf + *pos,rest))
          return 1;
        *pos += rest;
      }
      break;
    }
    if (f > *pos)
    {
      // Gap bytes between units (shouldn't happen): preserve.
      if (write_es_bytes(output,buf + *pos,f - *pos))
        return 1;
    }
    if (parse_pes_header(buf,blen,f,pend,pend_len,hdr_total,
                         pos,unit_left,FALSE))
      break;             // staged for the next packet
  }
  return 0;
}

/*
 * Extract all the TS packets for either a video or audio stream.
 *
 * Returns 0 if all went well, 1 if something went wrong.
 */
static int extract_av_via_pes(char  *input_name,
                              char  *output_name,
                              int    want_video,
                              int    quiet)
{
  int          err;
  PES_reader_p reader = NULL;
  ES_p         es = NULL;
  FILE        *output;

  if (!want_video)
  {
    print_err("### Audio output is not supported via PES in this utility\n");
    return 1;
  }

  output = fopen(output_name,"wb");
  if (output == NULL)
  {
    fprint_err("### Unable to open output file %s: %s\n",output_name,
               strerror(errno));
    return 1;
  }
  
  err = open_PES_reader(input_name,!quiet,!quiet,&reader);
  if (err)
  {
    fprint_err("### Error opening file %s\n",input_name);
    fclose(output);
    return 1;
  }

  set_PES_reader_video_only(reader,TRUE);

  // Wrap our PES stream up as an ES stream
  err = build_elementary_stream_PES(reader,&es);
  if (err)
  {
    print_err("### Error trying to build ES reader from PES reader\n");
    (void) close_PES_reader(&reader);
    (void) fclose(output);
    return 1;
  }

  for (;;)
  {
    ES_unit_p  unit;
    err = find_and_build_next_ES_unit(es,&unit);
    if (err == EOF)
      break;
    else if (err)
    {
      print_err("### Error reading next ES unit\n");
      (void) fclose(output);
      (void) close_PES_reader(&reader);
      close_elementary_stream(&es);
      return 1;
    }
    err = write_ES_unit(output,unit);
    if (err)
    {
      print_err("### Error writing ES unit out to file\n");
      free_ES_unit(&unit);
      (void) fclose(output);
      (void) close_PES_reader(&reader);
      close_elementary_stream(&es);
      return 1;
    }
    free_ES_unit(&unit);
  }

  (void) fclose(output);              // naughtily ignore the return code
  (void) close_PES_reader(&reader);   // naughtily ignore the return code
  close_elementary_stream(&es);
  return 0;
}

/*
 * Extract all the TS packets for a nominated PID to another file.
 *
 * Returns 0 if all went well, 1 if something went wrong.
 */
static int extract_pid_packets(TS_reader_p  tsreader,
                               FILE        *output,
                               uint32_t     pid_wanted,
                               int          max,
                               int          verbose,
                               int          quiet)
{
  int    err;
  int    count = 0;
  int    extracted = 0;
  // H.222.0 PES-unwrap state. A PES header (max 9 + 255 = 264 bytes)
  // can straddle TS packet boundaries, so header bytes are staged here
  // (from the start code) until the header is complete.
  byte   pes_pend[288];
  int    pes_pend_len  = 0;   // staged header bytes
  int    pes_hdr_total = 0;   // staged header size (9 + hd); 0 = unknown
  int    pes_unit_left = 0;   // ES bytes remaining for the current unit
  int    pes_unit_open = FALSE;
  // Sticky stream-type detection for the ADTS guard: ADTS and
  // PES-wrapped streams are byte-indistinguishable in a single packet
  // (an H.264 payload can begin with FF F0..FF just like ADTS, and an
  // AAC frame body can contain '00 00 01' runs that look like PES
  // candidates). First PES start code seen wins: it turns ADTS
  // treatment off for good. A stream whose first few PUSI payloads all
  // begin with the ADTS sync and yield no start code is treated as
  // unwrapped ADTS.
  int    adts_stream = FALSE;
  int    pes_stream = FALSE;
  int    pusi_seen = 0;
  // It doesn't make sense to start outputting data for our PID until we
  // get the start of a packet
  int    need_packet_start = TRUE;
  
  for (;;)
  {
    uint32_t pid;
    int      payload_unit_start_indicator;
    byte    *adapt, *payload;
    int      adapt_len, payload_len;
    
    if (max > 0 && count >= max)
    {
      if (!quiet) fprint_msg("Stopping after %d packets\n",max);
      break;
    }

    err = get_next_TS_packet(tsreader,&pid,
                             &payload_unit_start_indicator,
                             &adapt,&adapt_len,&payload,&payload_len);
    if (err == EOF)
      break;
    else if (err)
    {
      print_err("### Error reading TS packet\n");
      return 1;
    }
    
    count++;

    // If the packet is empty, all we can do is ignore it
    if (payload_len == 0)
      continue;

    if (pid == pid_wanted)
    {
      if (verbose)
      {
        fprint_msg("%4d: TS Packet PID %04x",count,pid);
        if (payload_unit_start_indicator)
          print_msg(" (start)");
        else if (need_packet_start)
          print_msg(" <ignored>");
        print_msg("\n");
      }


      if (payload_unit_start_indicator)
      {
        // A PUSI marks a TS packet containing the start of an
        // elementary stream unit. In H.222.0 a PES start code
        // ('00 00 01' + stream id) may appear anywhere in the payload
        // - the bytes before it are the tail of the previous unit and
        // must be preserved. A start code (or even the whole header)
        // can straddle into the next TS packet; partial bytes are
        // staged in pes_pend until the header is complete. Unwrapped
        // streams (ADTS audio per ISO/IEC 13818-7, some raw muxes)
        // have no PES header at all.
        byte buf[288 + 204];
        int  blen;
        int  had_pend;

        if (need_packet_start)
          need_packet_start = FALSE;

        if (!pes_stream && !adts_stream)
        {
          pusi_seen ++;
          if (find_pes_start(payload,payload_len,0) >= 0)
          {
            pes_stream = TRUE;
            if (verbose)
              fprint_msg("PES start code found - treating as PES stream\n");
          }
          else if (pusi_seen >= 4 && payload_len >= 2 &&
                   payload[0] == 0xFF && (payload[1] & 0xF0) == 0xF0)
          {
            adts_stream = TRUE;
            if (verbose)
              fprint_msg("No PES start code in first %d PUSI packets -\n"
                         "treating as unwrapped AAC (ADTS)\n",pusi_seen);
          }
        }
        if (adts_stream)
        {
          // Unwrapped AAC (ADTS, ISO/IEC 13818-7): the unit starts with
          // the 0xFFF sync. Never scan an ADTS payload for a "PES"
          // start - AAC frame bodies can contain '00 00 01' byte runs.
          if (verbose)
            fprint_msg("Unwrapped AAC (ADTS) - passing raw data\n");
          pes_unit_open = FALSE;
          pes_unit_left = 0;
          if (write_es_bytes(output,payload,payload_len))
            return 1;
          extracted ++;
          continue;
        }

        had_pend = pes_pend_len;
        blen = had_pend;
        memcpy(buf,pes_pend,had_pend);
        memcpy(buf + had_pend,payload,payload_len);
        blen += payload_len;
        pes_pend_len = 0;

        do
        {
          int  pos = 0;
          int  f;
          int  unit_pos;
          int  unit_left;

          if (had_pend >= 4)
          {
            // A partial PES header staged from the previous packet
            // (start code + id are within the staged bytes).
            if (parse_pes_header(buf,blen,0,pes_pend,&pes_pend_len,
                                 &pes_hdr_total,&unit_pos,&unit_left,
                                 verbose))
              break;             // staged for the next packet
            pos = unit_pos;
            pes_unit_left = unit_left;
            pes_unit_open = TRUE;
          }
          else if (had_pend > 0)
          {
            // A partial start code (1-3 staged bytes) staged from the
            // previous packet.
            f = find_pes_start(buf,blen,0);
            if (f < 0)
            {
              // Still incomplete: a start code straddling 3+ packets is
              // pathological - flush everything (staged bytes included)
              // as ES and give up staging.
              if (write_es_bytes(output,buf,blen))
                return 1;
              break;
            }
            if (f > had_pend)
            {
              // The staged bytes were not part of the start code after
              // all: they are ES (tail of the previous unit) - write
              // them with the payload bytes before the start code.
              if (write_es_bytes(output,buf,f))
                return 1;
            }
            if (parse_pes_header(buf,blen,f,pes_pend,&pes_pend_len,
                                 &pes_hdr_total,&unit_pos,&unit_left,
                                 verbose))
              break;             // staged for the next packet
            pos = unit_pos;
            pes_unit_left = unit_left;
            pes_unit_open = TRUE;
          }
          else if (!pes_unit_open)
          {
            // Fresh start: find the unit's start code.
            f = find_pes_start(buf,blen,0);
            if (f < 0)
            {
              // No start code: raw data (unwrapped stream, or a start
              // code straddling into the next packet). We must NOT
              // read buf[4..5] as a "PES packet length": for unwrapped
              // streams those are just ES bytes, and clamping
              // continuation packets to it silently dropped data -
              // this used to mangle every ADTS frame and lost chunks
              // of raw H.264 streams.
              if (verbose)
                fprint_msg("No PES header at unit start - passing raw data\n");
              pes_unit_open = FALSE;
              pes_unit_left = 0;
              if (write_es_bytes(output,buf,blen))
                return 1;
              break;
            }
            if (f > 0)
            {
              // Preserve the bytes before the PES start (tail of the
              // previous unit) - the old code assumed the header was
              // at payload[0] and dropped them.
              if (verbose)
                fprint_msg("PES start at offset %d\n",f);
              if (write_es_bytes(output,buf,f))
                return 1;
            }
            pes_unit_open = TRUE;
            if (parse_pes_header(buf,blen,f,pes_pend,&pes_pend_len,
                                 &pes_hdr_total,&pos,&pes_unit_left,
                                 verbose))
              break;             // staged for the next packet
          }
          else
          {
            // A unit from a previous packet is in flight; this PUSI
            // packet carries its tail and the start of the next unit.
            f = find_pes_start(buf,blen,0);
            if (f < 0)
            {
              if (pes_unit_left > 0 && pes_unit_left <= blen)
              {
                // The in-flight unit (declared length) ends inside
                // this packet; anything after it is a start code
                // straddling into the next packet (at most 3 bytes).
                int rest = blen - pes_unit_left;
                if (write_es_bytes(output,buf,pes_unit_left))
                  return 1;
                pes_unit_left = 0;
                pes_unit_open = FALSE;
                if (rest <= 3 && rest > 0)
                {
                  memcpy(pes_pend,buf + blen - rest,rest);
                  pes_pend_len = rest;
                  pes_hdr_total = 0;
                }
                else if (rest > 3)
                {
                  // No start code here (malformed): preserve bytes.
                  if (write_es_bytes(output,buf + (blen - rest),rest))
                    return 1;
                }
              }
              else
              {
                // The unit (unknown length, or longer than this
                // packet) carries on: raw.
                if (write_es_bytes(output,buf,blen))
                  return 1;
                if (pes_unit_left > 0)
                  pes_unit_left -= blen;
              }
              break;
            }
            {
              int lead = f;
              if (pes_unit_left > 0)
              {
                // The in-flight unit ends at or before the start code.
                if (pes_unit_left < f)
                  lead = pes_unit_left;
                pes_unit_left = 0;
              }
              if (lead > 0 && write_es_bytes(output,buf,lead))
                return 1;
              if (f > lead &&
                  write_es_bytes(output,buf + lead,f - lead))
                return 1;        // gap bytes (shouldn't happen)
              pes_unit_open = TRUE;
              if (parse_pes_header(buf,blen,f,pes_pend,&pes_pend_len,
                                   &pes_hdr_total,&pos,&pes_unit_left,
                                   verbose))
                break;           // staged for the next packet
            }
          }

          if (emit_unit_es(buf,blen,&pos,pes_pend,&pes_pend_len,
                           &pes_hdr_total,&pes_unit_left,output))
            return 1;
        } while (0);
        extracted ++;
        continue;
      }
      else
      {
        byte buf[288 + 204];
        int  blen;
        int  had_pend;
        int  pos;

        // If we haven't *started* a packet, we can't use this,
        // since it will just look like random bytes when written out.
        if (need_packet_start)
          {
            continue;
          }

        had_pend = pes_pend_len;
        blen = had_pend;
        memcpy(buf,pes_pend,had_pend);
        memcpy(buf + had_pend,payload,payload_len);
        blen += payload_len;
        pes_pend_len = 0;

        pos = 0;
        if (had_pend > 0)
        {
          int  f;
          int  unit_pos;
          int  unit_left;

          if (had_pend >= 4)
          {
            // Complete a partial PES header staged from the previous
            // packet (start code + id are within the staged bytes).
            if (parse_pes_header(buf,blen,0,pes_pend,&pes_pend_len,
                                 &pes_hdr_total,&unit_pos,&unit_left,
                                 verbose))
              {
                extracted ++;
                continue;        // staged for the next packet
              }
            pos = unit_pos;
            pes_unit_left = unit_left;
            pes_unit_open = TRUE;
          }
          else
          {
            // Complete a partial start code staged from the previous
            // packet.
            f = find_pes_start(buf,blen,0);
            if (f < 0)
            {
              // Still incomplete: a start code straddling 3+ packets is
              // pathological - flush everything (staged bytes included)
              // as ES and give up staging.
              if (write_es_bytes(output,buf,blen))
                return 1;
              extracted ++;
              continue;
            }
            if (f > had_pend)
            {
              // The staged bytes were not part of the start code after
              // all: they are ES (tail of the previous unit).
              if (write_es_bytes(output,buf,f))
                return 1;
            }
            if (parse_pes_header(buf,blen,f,pes_pend,&pes_pend_len,
                                 &pes_hdr_total,&unit_pos,&unit_left,
                                 verbose))
              {
                extracted ++;
                continue;        // staged for the next packet
              }
            pos = unit_pos;
            pes_unit_left = unit_left;
            pes_unit_open = TRUE;
          }
        }
        else if (!pes_unit_open)
        {
          // A continuation with no unit in flight (stream started
          // mid-flight, or a raw unwrapped stream): pass through.
          if (verbose)
            print_data(TRUE,"Data",payload,payload_len,1000);
          if (write_es_bytes(output,payload,payload_len))
            return 1;
          extracted ++;
          continue;
        }

        {
          int avail = blen - pos;
          int w = avail;
          if (pes_unit_left > 0 && w > pes_unit_left)
            w = pes_unit_left;
          if (write_es_bytes(output,buf + pos,w))
            return 1;
          pos += w;
          if (pes_unit_left > 0)
          {
            pes_unit_left -= w;
          }
          else
          {
            // The unit ended inside this continuation packet (only
            // possible for declared-length units): the trailing bytes
            // are a start code straddling the next packet (hold them)
            // or malformed (preserve them).
            int  rest = blen - pos;
            int  prefix = 0;

            if (rest == 3 && buf[pos] == 0 && buf[pos+1] == 0 &&
                buf[pos+2] == 1)
              prefix = 3;
            else
              while (prefix < rest && buf[pos + prefix] == 0)
                prefix ++;
            if (prefix > 0 && prefix == rest)
            {
              memcpy(pes_pend,buf + pos,rest);
              pes_pend_len = rest;
              pes_hdr_total = 0;
            }
            else if (rest > 0)
            {
              if (write_es_bytes(output,buf + pos,rest))
                return 1;
            }
          }
        }
        extracted ++;
      }
    }
  }

  if (!quiet)
    fprint_msg("Extracted %d of %d TS packet%s\n",
               extracted,count,(count==1?"":"s"));

  // If the user has forgotten to say -pid XX, or -video/-audio,
  // and are piping the output to another program, it can be surprising
  // if there is no data!
  if (quiet && extracted == 0)
    fprint_err("### No data extracted for PID %#04x (%d)\n",
               pid_wanted,pid_wanted);
  return 0;
}

/*
 * Extract all the TS packets for either a video or audio stream.
 *
 * Returns 0 if all went well, 1 if something went wrong.
 */
static int extract_av(int   input,
                      FILE *output,
                      int   want_video,
                      int   max,
                      int   verbose,
                      int   quiet)
{
  int      err, ii;
  int      max_to_read = max;
  int      total_num_read = 0;
  uint32_t pid = 0;
  TS_reader_p tsreader = NULL;
  pmt_p       pmt = NULL;

  // Turn our file into a TS reader
  err = build_TS_reader(input,&tsreader);
  if (err) return 1;

  // First, find out what program streams we actually have
  for (;;)
  {
    int  num_read;

    // Give up if we've read more than our limit
    if (max > 0 && max_to_read <= 0)
      break;

    err = find_pmt(tsreader, 1, max_to_read,verbose,quiet,&num_read,&pmt);
    if (err == EOF)
    {
      if (!quiet)
        print_msg("No program stream information in the input file\n");
      free_TS_reader(&tsreader);
      free_pmt(&pmt);
      return 0;
    }
    else if (err)
    {
      print_err("### Error finding program stream information\n");
      free_TS_reader(&tsreader);
      free_pmt(&pmt);
      return 1;
    }
    max_to_read -= num_read;
    total_num_read += num_read;

    // From that, find a stream of the type we want...
    // Note that the audio detection will accept either DVB or ADTS Dolby (AC-3)
    // stream types
    for (ii=0; ii < pmt->num_streams; ii++)
    {
      if (( want_video && IS_VIDEO_STREAM_TYPE(pmt->streams[ii].stream_type)) ||
          (!want_video && (IS_AUDIO_STREAM_TYPE(pmt->streams[ii].stream_type))))
      {
        pid = pmt->streams[ii].elementary_PID;
        break;
      }
    }
    free_pmt(&pmt);

    // Did we find what we want? If not, go round again and look for the
    // next PMT (subject to the number of records we're willing to search)
    if (pid != 0)
      break;
  }

  if (pid == 0)
  {
    fprint_err("### No %s stream specified in first %d TS packets in input file\n",
               (want_video?"video":"audio"),max);
    free_TS_reader(&tsreader);
    return 1;
  }

  if (!quiet)
    fprint_msg("Extracting %s PID %04x (%d)\n",(want_video?"video":"audio"),
               pid,pid);

  // Amend max to take account of the packets we've already read
  max -= total_num_read;

  // And do the extraction.
  err = extract_pid_packets(tsreader,output,pid,max,verbose,quiet);
  free_TS_reader(&tsreader);
  return err;
}

/*
 * Extract all the TS packets for a nominated PID to another file.
 *
 * Returns 0 if all went well, 1 if something went wrong.
 */
static int extract_pid(int          input,
                       FILE        *output,
                       uint32_t     pid_wanted,
                       int          max,
                       int          verbose,
                       int          quiet)
{
  int    err;
  TS_reader_p tsreader = NULL;

  // Turn our file into a TS reader
  err = build_TS_reader(input,&tsreader);
  if (err) return 1;

  err = extract_pid_packets(tsreader,output,pid_wanted,max,verbose,quiet);

  free_TS_reader(&tsreader);
  return err;
}

static void print_usage()
{
  print_msg(
    "Usage: ts2es [switches] [<infile>] [<outfile>]\n"
    "\n"
    );
  REPORT_VERSION("ts2es");
  print_msg(
    "\n"
    "  Extract a single (elementary) program stream from a Transport Stream\n"
    "  (or Program Stream).\n"
    "\n"
    "Files:\n"
    "  <infile>  is an H.222 Transport Stream file (but see -stdin and -pes)\n"
    "  <outfile> is a single elementary stream file (but see -stdout)\n"
    "\n"
    "Which stream to extract:\n"
    "  -pid <pid>         Output data for the stream with the given\n"
    "                     <pid>. Use -pid 0x<pid> to specify a hex value\n"
    "  -video             Output data for the (first) video stream\n"
    "                     named in the (first) PMT. This is the default.\n"
    "  -audio             Output data for the (first) audio stream\n"
    "                     named in the (first) PMT\n"
    "\n"
    "General switches:\n"
    "  -err stdout        Write error messages to standard output (the default)\n"
    "  -err stderr        Write error messages to standard error (Unix traditional)\n"
    "  -stdin             Input from standard input, instead of a file\n"
    "  -stdout            Output to standard output, instead of a file\n"
    "                     Forces -quiet and -err stderr.\n"
    "  -verbose, -v       Output informational/diagnostic messages\n"
    "  -quiet, -q         Only output error messages\n"
    "  -max <n>, -m <n>   Maximum number of TS packets to read\n"
    "\n"
    "  -pes, -ps          Use the PES interface to read ES units from\n"
    "                     the input file. This allows PS data to be read\n"
    "                     (there is no point in using this for TS data).\n"
    "                     Does not support -pid, -stdin or -stdout.\n"
    );
}

int main(int argc, char **argv)
{
  int    use_stdout = FALSE;
  int    use_stdin = FALSE;
  char  *input_name = NULL;
  char  *output_name = NULL;
  int    had_input_name = FALSE;
  int    had_output_name = FALSE;
  char  *action_switch = "None";

  EXTRACT   extract = EXTRACT_VIDEO; // What we're meant to extract
  int       input   = -1;    // Our input file descriptor
  FILE     *output  = NULL;  // The stream we're writing to (if any)
  int       max     = 0;     // The maximum number of TS packets to read (or 0)
  uint32_t  pid     = 0;     // The PID of the (single) stream to extract
  int       quiet   = FALSE; // True => be as quiet as possible
  int       verbose = FALSE; // True => output diagnostic/progress messages
  int       use_pes = FALSE;

  int    err = 0;
  int    ii = 1;

  if (argc < 2)
  {
    print_usage();
    return 0;
  }

  while (ii < argc)
  {
    if (argv[ii][0] == '-')
    {
      if (!strcmp("--help",argv[ii]) || !strcmp("-h",argv[ii]) ||
          !strcmp("-help",argv[ii]))
      {
        print_usage();
        return 0;
      }
      else if (!strcmp("-verbose",argv[ii]) || !strcmp("-v",argv[ii]))
      {
        verbose = TRUE;
        quiet = FALSE;
      }
      else if (!strcmp("-quiet",argv[ii]) || !strcmp("-q",argv[ii]))
      {
        verbose = FALSE;
        quiet = TRUE;
      }
      else if (!strcmp("-max",argv[ii]) || !strcmp("-m",argv[ii]))
      {
        CHECKARG("ts2es",ii);
        err = int_value("ts2es",argv[ii],argv[ii+1],TRUE,10,&max);
        if (err) return 1;
        ii++;
      }
      else if (!strcmp("-pes",argv[ii]) || !strcmp("-ps",argv[ii]))
      {
        use_pes = TRUE;
      }
      else if (!strcmp("-pid",argv[ii]))
      {
        CHECKARG("ts2es",ii);
        err = unsigned_value("ts2es",argv[ii],argv[ii+1],0,&pid);
        if (err) return 1;
        ii++;
        extract = EXTRACT_PID;
      }
      else if (!strcmp("-video",argv[ii]))
      {
        extract = EXTRACT_VIDEO;
      }
      else if (!strcmp("-audio",argv[ii]))
      {
        extract = EXTRACT_AUDIO;
      }
      else if (!strcmp("-stdin",argv[ii]))
      {
        use_stdin = TRUE;
        had_input_name = TRUE;  // so to speak
      }
      else if (!strcmp("-stdout",argv[ii]))
      {
        use_stdout = TRUE;
        had_output_name = TRUE;  // so to speak
        redirect_output_stderr();
      }
      else if (!strcmp("-err",argv[ii]))
      {
        CHECKARG("ts2es",ii);
        if (!strcmp(argv[ii+1],"stderr"))
          redirect_output_stderr();
        else if (!strcmp(argv[ii+1],"stdout"))
          redirect_output_stdout();
        else
        {
          fprint_err("### ts2es: "
                     "Unrecognised option '%s' to -err (not 'stdout' or"
                     " 'stderr')\n",argv[ii+1]);
          return 1;
        }
        ii++;
      }
      else
      {
        fprint_err("### ts2es: "
                   "Unrecognised command line switch '%s'\n",argv[ii]);
        return 1;
      }
    }
    else
    {
      if (had_input_name && had_output_name)
      {
        fprint_err("### ts2es: Unexpected '%s'\n",argv[ii]);
        return 1;
      }
      else if (had_input_name)  // shouldn't do this if had -stdout
      {
        output_name = argv[ii];
        had_output_name = TRUE;
      }
      else
      {
        input_name = argv[ii];
        had_input_name = TRUE;
      }
    }
    ii++;
  }

  if (!had_input_name)
  {
    print_err("### ts2es: No input file specified\n");
    return 1;
  }

  if (!had_output_name)
  {
    fprint_err("### ts2es: "
               "No output file specified for %s\n",action_switch);
    return 1;
  }

  // ============================================================
  // Testing PES output
  if (use_pes && extract == EXTRACT_PID)
  {
    print_err("### ts2es: -pid is not supported with -pes\n");
    return 1;
  }
  if (use_pes && use_stdout)
  {
    print_err("### ts2es: -stdout is not supported with -pes\n");
    return 1;
  }
  if (use_pes && use_stdin)
  {
    print_err("### ts2es: -stdin is not supported with -pes\n");
    return 1;
  }
  if (use_pes)
  {
    err = extract_av_via_pes(input_name,output_name,(extract==EXTRACT_VIDEO),
                             quiet);
    if (err)
    {
      print_err("### ts2es: Error writing via PES\n");
      return 1;
    }
    return 0;
  }
  // ============================================================
  
  // Try to stop extraneous data ending up in our output stream
  if (use_stdout)
  {
    verbose = FALSE;
    quiet = TRUE;
  }

  if (use_stdin)
    input = STDIN_FILENO;
  else
  {
    input = open_binary_file(input_name,FALSE);
    if (input == -1)
    {
      fprint_err("### ts2es: Unable to open input file %s\n",input_name);
      return 1;
    }
  }
  if (!quiet)
    fprint_msg("Reading from %s\n",(use_stdin?"<stdin>":input_name));

  if (had_output_name)
  {
    if (use_stdout)
      output = stdout;
    else
    {
      output = fopen(output_name,"wb");
      if (output == NULL)
      {
        if (!use_stdin) (void) close_file(input);
        fprint_err("### ts2es: "
                   "Unable to open output file %s: %s\n",output_name,
                   strerror(errno));
        return 1;
      }
    }
    if (!quiet)
      fprint_msg("Writing to   %s\n",(use_stdout?"<stdout>":output_name));
  }

  if (!quiet)
  {
    if (extract == EXTRACT_PID)
      fprint_msg("Extracting packets for PID %04x (%d)\n",pid,pid);
    else
      fprint_msg("Extracting %s\n",(extract==EXTRACT_VIDEO?"video":"audio"));
  }
  
  if (max && !quiet)
    fprint_msg("Stopping after %d TS packets\n",max);

  if (extract == EXTRACT_PID)
    err = extract_pid(input,output,pid,max,verbose,quiet);
  else
    err = extract_av(input,output,(extract==EXTRACT_VIDEO),
                     max,verbose,quiet);
  if (err)
  {
    print_err("### ts2es: Error extracting data\n");
    if (!use_stdin)  (void) close_file(input);
    if (!use_stdout) (void) fclose(output);
    return 1;
  }

  // And tidy up when we're finished
  if (!use_stdout)
  {
    errno = 0;
    err = fclose(output);
    if (err)
    {
      fprint_err("### ts2es: Error closing output file %s: %s\n",
                 output_name,strerror(errno));
      (void) close_file(input);
      return 1;
    }
  }
  if (!use_stdin)
  {
    err = close_file(input);
    if (err)
      fprint_err("### ts2es: Error closing input file %s\n",input_name);
  }
  return 0;
}

// Local Variables:
// tab-width: 8
// indent-tabs-mode: nil
// c-basic-offset: 2
// End:
// vim: set tabstop=8 shiftwidth=2 expandtab:
