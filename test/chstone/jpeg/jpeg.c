/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */


/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
/*
 * Definition of parameters
 *
 *  @(#) $Id: global.h,v 1.2 2003/07/18 10:19:21 honda Exp $
 */
#ifndef _GLOBAL_H_
#define _GLOBAL_H_

int main_result;


/*
 * Size of JPEG file
 */
#define JPEG_FILE_SIZE  7506

/*
 * Size of output buffer (for every element)
 */
#define BMP_OUT_SIZE  7506


#endif /* _GLOBAL_H_ */
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
/*
 *  Header file for decoding
 *
 *  @(#) $Id: decode.h,v 1.2 2003/07/18 10:19:21 honda Exp $
 */

#ifndef _DECODE_H_
#define _DECODE_H_


#define NUM_HUFF_TBLS       2
#define NUM_QUANT_TBLS      4
#define DCTSIZE             8
#define DCTSIZE2           64

/*
 * Define the number of components as 3
 */
#define NUM_COMPONENT       3

/*
 * Define the RGB number as 3
 */
#define RGB_NUM  3

/*
 * Define the sample precision as 8
 */
#define IDCT_SHIFT 128
#define IDCT_BOUNT 255
#define MARKER_MARKER 0xff

int OutData_image_width;
int OutData_image_height;
int OutData_comp_vpos[RGB_NUM];
int OutData_comp_hpos[RGB_NUM];
unsigned char OutData_comp_buf[RGB_NUM][BMP_OUT_SIZE];

#define SF1_1_1 0
#define SF4_1_1 2

short DecodeInfo_image_height;
short DecodeInfo_image_width;
char DecodeInfo_data_precision;
char DecodeInfo_num_components;
int DecodeInfo_smp_fact;
int DecodeInfo_comps_info_index[NUM_COMPONENT];
char DecodeInfo_comps_info_id[NUM_COMPONENT];
char DecodeInfo_comps_info_h_samp_factor[NUM_COMPONENT];
char DecodeInfo_comps_info_v_samp_factor[NUM_COMPONENT];
char DecodeInfo_comps_info_quant_tbl_no[NUM_COMPONENT];
char DecodeInfo_comps_info_dc_tbl_no[NUM_COMPONENT];
char DecodeInfo_comps_info_ac_tbl_no[NUM_COMPONENT];
unsigned int DecodeInfo_quant_tbl_quantval[NUM_QUANT_TBLS][DCTSIZE2];
int DecodeInfo_dc_xhuff_tbl_bits[NUM_HUFF_TBLS][36];
int DecodeInfo_dc_xhuff_tbl_huffval[NUM_HUFF_TBLS][257];
int DecodeInfo_ac_xhuff_tbl_bits[NUM_HUFF_TBLS][36];
int DecodeInfo_ac_xhuff_tbl_huffval[NUM_HUFF_TBLS][257];
int DecodeInfo_dc_dhuff_tbl_ml[NUM_HUFF_TBLS];
int DecodeInfo_dc_dhuff_tbl_maxcode[NUM_HUFF_TBLS][36];
int DecodeInfo_dc_dhuff_tbl_mincode[NUM_HUFF_TBLS][36];
int DecodeInfo_dc_dhuff_tbl_valptr[NUM_HUFF_TBLS][36];
int DecodeInfo_ac_dhuff_tbl_ml[NUM_HUFF_TBLS];
int DecodeInfo_ac_dhuff_tbl_maxcode[NUM_HUFF_TBLS][36];
int DecodeInfo_ac_dhuff_tbl_mincode[NUM_HUFF_TBLS][36];
int DecodeInfo_ac_dhuff_tbl_valptr[NUM_HUFF_TBLS][36];
int DecodeInfo_MCUWidth;
int DecodeInfo_MCUHeight;
int DecodeInfo_NumMCU;

void decode_start ();
void read_markers (unsigned char *buf);

#endif /* _DECODE_H_ */



/*
 * Output Buffer
 */
unsigned char *CurHuffReadBuf;




/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 *  Read the head of the marker
 *
 *  @(#) $Id: marker.c,v 1.2 2003/07/18 10:19:21 honda Exp $
 */
/*************************************************************
Copyright (C) 1990, 1991, 1993 Andy C. Hung, all rights reserved.
PUBLIC DOMAIN LICENSE: Stanford University Portable Video Research
Group. If you use this software, you agree to the following: This
program package is purely experimental, and is licensed "as is".
Permission is granted to use, modify, and distribute this program
without charge for any purpose, provided this license/ disclaimer
notice appears in the copies.  No warranty or maintenance is given,
either expressed or implied.  In no event shall the author(s) be
liable to you or a third party for any special, incidental,
consequential, or other damages, arising out of the use or inability
to use the program for any purpose (or the loss of data), even if we
have been advised of such possibilities.  Any public reference or
advertisement of this source code should refer to it as the Portable
Video Research Group (PVRG) code, and not by any author(s) (or
Stanford University) name.
*************************************************************/
/*
************************************************************
marker.c

This file contains the Marker library which uses the direct buffer
access routines bgetc...

************************************************************
*/

/* Only for the marker needed at the baseline */
typedef enum
{				/* JPEG marker codes */
  M_SOI = 0xd8,			/* Start of Image */
  M_SOF0 = 0xc0,		/* Baseline DCT ( Huffman )  */
  M_SOS = 0xda,			/* Start of Scan ( Head of Compressed Data )  */
  M_DHT = 0xc4,			/* Huffman Table */
  M_DQT = 0xdb,			/* Quantization Table */
  M_EOI = 0xd9			/* End of Image */
} JPEG_MARKER;


/*
 * Initialize Quantization Table
 */
const int izigzag_index[64] = {
  0, 1, 8, 16, 9, 2, 3, 10,
  17, 24, 32, 25, 18, 11, 4, 5,
  12, 19, 26, 33, 40, 48, 41, 34,
  27, 20, 13, 6, 7, 14, 21, 28,
  35, 42, 49, 56, 57, 50, 43, 36,
  29, 22, 15, 23, 30, 37, 44, 51,
  58, 59, 52, 45, 38, 31, 39, 46,
  53, 60, 61, 54, 47, 55, 62, 63
};

/*
+--------------------------------------------------------------------------+
| * Test Vector (added for CHStone)                                        |
|     out_length : expected output data                                    |
|                  for "get_sof", "get_sos", "get_dht" and "get_dqt"       |
+--------------------------------------------------------------------------+
*/
const int out_length[8] = { 65, 65, 17, 29, 179, 29, 179, 12 };

/*
+--------------------------------------------------------------------------+
| * Test Vector (added for CHStone)                                        |
|     out_prec : expected output data for "get_dqt"                        |
+--------------------------------------------------------------------------+
*/
const int out_prec[2] = { 0, 0 };

/*
+--------------------------------------------------------------------------+
| * Test Vectors (added for CHStone)                                       |
|     out_h_samp_factor : expected output data for "get_sof"               |
|     out_v_samp_factor : expected output data for "get_sof"               |
|     out_quant_tbl_no : expected output data for "get_sof"                |
+--------------------------------------------------------------------------+
*/
const int out_h_samp_factor[3] = { 2, 1, 1 };
const int out_v_samp_factor[3] = { 2, 1, 1 };
const int out_quant_tbl_no[3] = { 0, 1, 1 };

/*
+--------------------------------------------------------------------------+
| * Test Vector (added for CHStone)                                        |
|     out_count : expected output data for "get_dht"                       |
+--------------------------------------------------------------------------+
*/
const int out_count[4] = { 12, 162, 12, 162 };

/*
+--------------------------------------------------------------------------+
| * Test Vectors (added for CHStone)                                       |
|     out_dc_tbl_no, out_ac_tbl_no : expected output data for "get_sos"    |
+--------------------------------------------------------------------------+
*/
const int out_dc_tbl_no[3] = { 0, 1, 1 };
const int out_ac_tbl_no[3] = { 0, 1, 1 };

/*
+--------------------------------------------------------------------------+
| * Test Vectors (added for CHStone)                                       |
|     out_data_precision : expected output data for "get_sof"              |
|     out_image_height : expected output data for "get_sof"                |
|     out_image_width : expected output data for "get_sof"                 |
|     out_num_components : expected output data for "get_sof"              |
+--------------------------------------------------------------------------+
*/
#define out_data_precision 8
#define out_image_height 113
#define out_image_width 150
#define out_num_components 3

int i0 = 0;
int i1 = 0;
int i2 = 0;

/*
 *  Read Buffer
 */
static unsigned char *ReadBuf;


/*
 *  Read from Buffer
 */
int
read_byte (void)
{
  return *ReadBuf++;
}


short
read_word (void)
{
  short c;

  c = *ReadBuf++ << 8;
  c |= *ReadBuf++;

  return c;
}

int
first_marker (void)
{
  int c1, c2;
  c1 = read_byte ();
  c2 = read_byte ();

  if (c1 != 0xFF || c2 != (int) M_SOI)
    {
      main_result++;
    }

  return c2;
}


int
next_marker (void)
{
  int c;

  for (;;)
    {
      c = read_byte ();

      while (c != 0xff)
	{
	  c = read_byte ();
	}

      do
	{
	  c = read_byte ();
	}
      while (c == 0xff);
      if (c != 0)
	{
	  break;
	}
    }
  return c;
}


/*
 *  Baseline DCT ( Huffman )  
 */
void
get_sof ()
{
  int ci, c, length;
  int *p_comp_info_index;
  char *p_comp_info_id;
  char *p_comp_info_h_samp_factor;
  char *p_comp_info_v_samp_factor;
  char *p_comp_info_quant_tbl_no;
  char *p_comp_info_dc_tbl_no;
  char *p_comp_info_ac_tbl_no;

  length = read_word ();
  DecodeInfo_data_precision = read_byte ();
  DecodeInfo_image_height = read_word ();
  DecodeInfo_image_width = read_word ();
  DecodeInfo_num_components = read_byte ();

  if (length != out_length[i0++])
    {
      main_result++;
    }
  if (DecodeInfo_data_precision != out_data_precision)
    {
      main_result++;
    }
  if (DecodeInfo_image_height != out_image_height)
    {
      main_result++;
    }
  if (DecodeInfo_image_width != out_image_width)
    {
      main_result++;
    }
  if (DecodeInfo_num_components != out_num_components)
    {
      main_result++;
    }

  length -= 8;

  /* Error check is omitted. */

  /* Check components */
  for (ci = 0; ci < DecodeInfo_num_components; ci++)
    {
      p_comp_info_index = &DecodeInfo_comps_info_index[ci];
      p_comp_info_id = &DecodeInfo_comps_info_id[ci];
      p_comp_info_h_samp_factor = &DecodeInfo_comps_info_h_samp_factor[ci];
      p_comp_info_v_samp_factor = &DecodeInfo_comps_info_v_samp_factor[ci];
      p_comp_info_quant_tbl_no = &DecodeInfo_comps_info_quant_tbl_no[ci];
      p_comp_info_dc_tbl_no = &DecodeInfo_comps_info_dc_tbl_no[ci];
      p_comp_info_ac_tbl_no = &DecodeInfo_comps_info_ac_tbl_no[ci];

      *p_comp_info_index = ci;
      *p_comp_info_id = read_byte ();
      c = read_byte ();
      *p_comp_info_h_samp_factor = (c >> 4) & 15;
      *p_comp_info_v_samp_factor = (c) & 15;
      *p_comp_info_quant_tbl_no = read_byte ();

      if (*p_comp_info_h_samp_factor != out_h_samp_factor[*p_comp_info_index])
	{
	  main_result++;
	}
      if (*p_comp_info_v_samp_factor != out_v_samp_factor[*p_comp_info_index])
	{
	  main_result++;
	}
      if (*p_comp_info_quant_tbl_no != out_quant_tbl_no[*p_comp_info_index])
	{
	  main_result++;
	}

    }


  /*
   *  Determinination of Sampling Factor
   *  Only 1_1_1 and 4_1_1 are supported
   */
  if (DecodeInfo_comps_info_h_samp_factor[0] == 2)
    {
      DecodeInfo_smp_fact = SF4_1_1;
    }
  else
    {
      DecodeInfo_smp_fact = SF1_1_1;
    }
}


void
get_sos ()
{
  int length, num_comp;
  int i, c, cc, ci, j;
  int *p_comp_info_index;
  char *p_comp_info_id;
  char *p_comp_info_h_samp_factor;
  char *p_comp_info_v_samp_factor;
  char *p_comp_info_quant_tbl_no;
  char *p_comp_info_dc_tbl_no;
  char *p_comp_info_ac_tbl_no;

  length = read_word ();
  num_comp = read_byte ();

  if (length != out_length[i0++])
    {
      main_result++;
    }

  /* Decode each component */
  for (i = 0; i < num_comp; i++)
    {
      cc = read_byte ();
      c = read_byte ();

      for (ci = 0; ci < DecodeInfo_num_components; ci++)
	{
	  p_comp_info_index = &DecodeInfo_comps_info_index[ci];
	  p_comp_info_id = &DecodeInfo_comps_info_id[ci];
	  p_comp_info_h_samp_factor =
	    &DecodeInfo_comps_info_h_samp_factor[ci];
	  p_comp_info_v_samp_factor =
	    &DecodeInfo_comps_info_v_samp_factor[ci];
	  p_comp_info_quant_tbl_no = &DecodeInfo_comps_info_quant_tbl_no[ci];
	  p_comp_info_dc_tbl_no = &DecodeInfo_comps_info_dc_tbl_no[ci];
	  p_comp_info_ac_tbl_no = &DecodeInfo_comps_info_ac_tbl_no[ci];

	  if (cc == *p_comp_info_id)
	    {
	      goto id_found;
	    }
	}

      main_result++;

    id_found:
      *p_comp_info_dc_tbl_no = (c >> 4) & 15;
      *p_comp_info_ac_tbl_no = (c) & 15;

      if (*p_comp_info_dc_tbl_no != out_dc_tbl_no[cc - 1])
	{
	  main_result++;
	}
      if (*p_comp_info_ac_tbl_no != out_ac_tbl_no[cc - 1])
	{
	  main_result++;
	}


    }

  /* pass parameters; Ss, Se, Ah and Al for progressive JPEG */
  j = 3;
  while (j--)
    {
      c = read_byte ();
    }

  /*
   * Define the Buffer at this point as the head of data
   */
  CurHuffReadBuf = ReadBuf;

}


/*
 * Get Huffman Table
 */
void
get_dht ()
{
  int length, index;
  int i, count;
  int *pp_xhtbl_bits;
  int *pp_xhtbl_huffval;

  length = read_word ();
  length -= 2;

  if (length != out_length[i0++])
    {
      main_result++;
    }


  while (length > 16)
    {
      index = read_byte ();

      if (index & 0x10)
	{
	  /* AC */
	  index -= 0x10;
	  pp_xhtbl_bits = DecodeInfo_ac_xhuff_tbl_bits[index];
	  pp_xhtbl_huffval = DecodeInfo_ac_xhuff_tbl_huffval[index];
	}
      else
	{
	  /* DC */
	  pp_xhtbl_bits = DecodeInfo_dc_xhuff_tbl_bits[index];
	  pp_xhtbl_huffval = DecodeInfo_dc_xhuff_tbl_huffval[index];
	}
      count = 0;

      for (i = 1; i <= 16; i++)
	{
	  pp_xhtbl_bits[i] = read_byte ();
	  count += pp_xhtbl_bits[i];
	}

      if (count != out_count[i2++])
	{
	  main_result++;
	}

      length -= 1 + 16;

      for (i = 0; i < count; i++)
	{
	  pp_xhtbl_huffval[i] = read_byte ();
	}

      length -= count;
    }
}


void
get_dqt ()
{
  int length, prec;
  int num, i;
  unsigned int tmp;
  unsigned int *p_quant_tbl;

  length = read_word ();
  length -= 2;

  if (length != out_length[i0++])
    {
      main_result++;
    }


  while (length > 0)
    {
      num = read_byte ();
      /* Precision 0:8bit, 1:16bit */
      prec = num >> 4;
      /* Table Number */
      num &= 0x0f;

      if (prec != out_prec[i1])
	{
	  main_result++;
	}
      if (prec != out_prec[i1++])
	{
	  main_result++;
	}

      p_quant_tbl = DecodeInfo_quant_tbl_quantval[num];
      for (i = 0; i < DCTSIZE2; i++)
	{
	  if (prec)
	    {
	      tmp = read_word ();
	    }
	  else
	    {
	      tmp = read_byte ();
	    }
	  p_quant_tbl[izigzag_index[i]] = (unsigned short) tmp;
	}
      length -= DCTSIZE2 + 1;
      if (prec)
	{
	  length -= DCTSIZE2;
	}
    }
}

void
read_markers (unsigned char *buf)
{
  int unread_marker;
  int sow_SOI;

  ReadBuf = buf;

  sow_SOI = 0;

  unread_marker = 0;

  /* Read the head of the marker */
  for (;;)
    {
      if (!sow_SOI)
	{
	  unread_marker = first_marker ();
	}
      else
	{
	  unread_marker = next_marker ();
	}

      switch (unread_marker)
	{
	case M_SOI:		/* Start of Image */
	  sow_SOI = 1;
	  break;

	case M_SOF0:		/* Baseline DCT ( Huffman )  */
	  get_sof ();
	  break;

	case M_SOS:		/* Start of Scan ( Head of Compressed Data )  */
	  get_sos ();
	  return;

	case M_DHT:
	  get_dht ();
	  break;

	case M_DQT:
	  get_dqt ();
	  break;

	case M_EOI:
	  return;
	}
    }
}
/*
+--------------------------------------------------------------------------+
| CHStone : A suite of Benchmark Programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remarks :                                                              |
|    1. This source code is reformatted to follow CHStone's style.         |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       successfully executed.                                             |
|    4. Follow the copyright of each benchmark program.                    |
+--------------------------------------------------------------------------+
*/
/*
 *  IDCT transformation of Chen algorithm
 *
 *  @(#) $Id: chenidct.c,v 1.2 2003/07/18 10:19:21 honda Exp $
 */
/*************************************************************
Copyright (C) 1990, 1991, 1993 Andy C. Hung, all rights reserved.
PUBLIC DOMAIN LICENSE: Stanford University Portable Video Research
Group. If you use this software, you agree to the following: This
program package is purely experimental, and is licensed "as is".
Permission is granted to use, modify, and distribute this program
without charge for any purpose, provided this license/ disclaimer
notice appears in the copies.  No warranty or maintenance is given,
either expressed or implied.  In no event shall the author(s) be
liable to you or a third party for any special, incidental,
consequential, or other damages, arising out of the use or inability
to use the program for any purpose (or the loss of data), even if we
have been advised of such possibilities.  Any public reference or
advertisement of this source code should refer to it as the Portable
Video Research Group (PVRG) code, and not by any author(s) (or
Stanford University) name.
*************************************************************/
/*
************************************************************
chendct.c

A simple DCT algorithm that seems to have fairly nice arithmetic
properties.

W. H. Chen, C. H. Smith and S. C. Fralick "A fast computational
algorithm for the discrete cosine transform," IEEE Trans. Commun.,
vol. COM-25, pp. 1004-1009, Sept 1977.

************************************************************
*/

#define LS(r,s) ((r) << (s))
#define RS(r,s) ((r) >> (s))	/* Caution with rounding... */

#define MSCALE(expr)  RS((expr),9)

/* Cos constants */

#define c1d4 362L

#define c1d8 473L
#define c3d8 196L

#define c1d16 502L
#define c3d16 426L
#define c5d16 284L
#define c7d16 100L


/*
 *
 * ChenIDCT() implements the Chen inverse dct. Note that there are two
 * input vectors that represent x=input, and y=output, and must be
 * defined (and storage allocated) before this routine is called.
 */
void
ChenIDct (int *x, int *y)
{
  register int i;
  register int *aptr;
  register int a0, a1, a2, a3;
  register int b0, b1, b2, b3;
  register int c0, c1, c2, c3;

  /* Loop over columns */

  for (i = 0; i < 8; i++)
    {
      aptr = x + i;
      b0 = LS (*aptr, 2);
      aptr += 8;
      a0 = LS (*aptr, 2);
      aptr += 8;
      b2 = LS (*aptr, 2);
      aptr += 8;
      a1 = LS (*aptr, 2);
      aptr += 8;
      b1 = LS (*aptr, 2);
      aptr += 8;
      a2 = LS (*aptr, 2);
      aptr += 8;
      b3 = LS (*aptr, 2);
      aptr += 8;
      a3 = LS (*aptr, 2);

      /* Split into even mode  b0 = x0  b1 = x4  b2 = x2  b3 = x6.
         And the odd terms a0 = x1 a1 = x3 a2 = x5 a3 = x7.
       */

      c0 = MSCALE ((c7d16 * a0) - (c1d16 * a3));
      c1 = MSCALE ((c3d16 * a2) - (c5d16 * a1));
      c2 = MSCALE ((c3d16 * a1) + (c5d16 * a2));
      c3 = MSCALE ((c1d16 * a0) + (c7d16 * a3));

      /* First Butterfly on even terms. */

      a0 = MSCALE (c1d4 * (b0 + b1));
      a1 = MSCALE (c1d4 * (b0 - b1));

      a2 = MSCALE ((c3d8 * b2) - (c1d8 * b3));
      a3 = MSCALE ((c1d8 * b2) + (c3d8 * b3));

      b0 = a0 + a3;
      b1 = a1 + a2;
      b2 = a1 - a2;
      b3 = a0 - a3;

      /* Second Butterfly */

      a0 = c0 + c1;
      a1 = c0 - c1;
      a2 = c3 - c2;
      a3 = c3 + c2;

      c0 = a0;
      c1 = MSCALE (c1d4 * (a2 - a1));
      c2 = MSCALE (c1d4 * (a2 + a1));
      c3 = a3;

      aptr = y + i;
      *aptr = b0 + c3;
      aptr += 8;
      *aptr = b1 + c2;
      aptr += 8;
      *aptr = b2 + c1;
      aptr += 8;
      *aptr = b3 + c0;
      aptr += 8;
      *aptr = b3 - c0;
      aptr += 8;
      *aptr = b2 - c1;
      aptr += 8;
      *aptr = b1 - c2;
      aptr += 8;
      *aptr = b0 - c3;
    }

  /* Loop over rows */

  for (i = 0; i < 8; i++)
    {
      aptr = y + LS (i, 3);
      b0 = *(aptr++);
      a0 = *(aptr++);
      b2 = *(aptr++);
      a1 = *(aptr++);
      b1 = *(aptr++);
      a2 = *(aptr++);
      b3 = *(aptr++);
      a3 = *(aptr);

      /*
         Split into even mode  b0 = x0  b1 = x4  b2 = x2  b3 = x6.
         And the odd terms a0 = x1 a1 = x3 a2 = x5 a3 = x7.
       */

      c0 = MSCALE ((c7d16 * a0) - (c1d16 * a3));
      c1 = MSCALE ((c3d16 * a2) - (c5d16 * a1));
      c2 = MSCALE ((c3d16 * a1) + (c5d16 * a2));
      c3 = MSCALE ((c1d16 * a0) + (c7d16 * a3));

      /* First Butterfly on even terms. */

      a0 = MSCALE (c1d4 * (b0 + b1));
      a1 = MSCALE (c1d4 * (b0 - b1));

      a2 = MSCALE ((c3d8 * b2) - (c1d8 * b3));
      a3 = MSCALE ((c1d8 * b2) + (c3d8 * b3));

      /* Calculate last set of b's */

      b0 = a0 + a3;
      b1 = a1 + a2;
      b2 = a1 - a2;
      b3 = a0 - a3;

      /* Second Butterfly */

      a0 = c0 + c1;
      a1 = c0 - c1;
      a2 = c3 - c2;
      a3 = c3 + c2;

      c0 = a0;
      c1 = MSCALE (c1d4 * (a2 - a1));
      c2 = MSCALE (c1d4 * (a2 + a1));
      c3 = a3;

      aptr = y + LS (i, 3);
      *(aptr++) = b0 + c3;
      *(aptr++) = b1 + c2;
      *(aptr++) = b2 + c1;
      *(aptr++) = b3 + c0;
      *(aptr++) = b3 - c0;
      *(aptr++) = b2 - c1;
      *(aptr++) = b1 - c2;
      *(aptr) = b0 - c3;
    }

  /*
     Retrieve correct accuracy. We have additional factor
     of 16 that must be removed.
   */

  for (i = 0, aptr = y; i < 64; i++, aptr++)
    {
      *aptr = (((*aptr < 0) ? (*aptr - 8) : (*aptr + 8)) / 16);
    }

}

 /*END*/
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
/*
 * Functions for Huffman decodeing
 *
 *  @(#) $Id: huffman.h,v 1.2 2003/07/18 10:19:21 honda Exp $
 */

void huff_make_dhuff_tb ();
void DecodeHuffMCU (int *out_buf, int num_cmp);
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*************************************************************
Copyright (C) 1990, 1991, 1993 Andy C. Hung, all rights reserved.
PUBLIC DOMAIN LICENSE: Stanford University Portable Video Research
Group. If you use this software, you agree to the following: This
program package is purely experimental, and is licensed "as is".
Permission is granted to use, modify, and distribute this program
without charge for any purpose, provided this license/ disclaimer
notice appears in the copies.  No warranty or maintenance is given,
either expressed or implied.  In no event shall the author(s) be
liable to you or a third party for any special, incidental,
consequential, or other damages, arising out of the use or inability
to use the program for any purpose (or the loss of data), even if we
have been advised of such possibilities.  Any public reference or
advertisement of this source code should refer to it as the Portable
Video Research Group (PVRG) code, and not by any author(s) (or
Stanford University) name.
*************************************************************/

/*
************************************************************
decode.c (original: transform.c)

This file contains the reference DCT, the zig-zag and quantization
algorithms.

************************************************************
*/
/*
 *  Decoder
 *
 *  @(#) $Id: decode.c,v 1.2 2003/07/18 10:19:21 honda Exp $
 */

void ChenIDct (int *x, int *y);
const int zigzag_index[64] =	/* Is zig-zag map for matrix -> scan array */
{ 0, 1, 5, 6, 14, 15, 27, 28,
  2, 4, 7, 13, 16, 26, 29, 42,
  3, 8, 12, 17, 25, 30, 41, 43,
  9, 11, 18, 24, 31, 40, 44, 53,
  10, 19, 23, 32, 39, 45, 52, 54,
  20, 22, 33, 38, 46, 51, 55, 60,
  21, 34, 37, 47, 50, 56, 59, 61,
  35, 36, 48, 49, 57, 58, 62, 63
};
int p_out_vpos, p_out_hpos;
unsigned char p_out_buf[BMP_OUT_SIZE];

/*
 * IZigzagMatrix() performs an inverse zig-zag translation on the
 * input imatrix and places the output in omatrix.
 */
void
IZigzagMatrix (int *imatrix, int *omatrix)
{
  int i;

  for (i = 0; i < DCTSIZE2; i++)
    {
      *(omatrix++) = imatrix[zigzag_index[i]];
    }
}


/*
 * IQuantize() takes an input matrix and does an inverse quantization
 * and puts the output int qmatrix.
 */
void
IQuantize (int *matrix, unsigned int *qmatrix)
{
  int *mptr;

  for (mptr = matrix; mptr < matrix + DCTSIZE2; mptr++)
    {
      *mptr = *mptr * (*qmatrix);
      qmatrix++;
    }
}


/*
 * PostshiftIDctMatrix() adds 128 (2048) to all 64 elements of an 8x8 matrix.
 * This results in strictly positive values for all pixel coefficients.
 */
void
PostshiftIDctMatrix (int *matrix, int shift)
{
  int *mptr;
  for (mptr = matrix; mptr < matrix + DCTSIZE2; mptr++)
    {
      *mptr += shift;
    }
}


/*
 * BoundIDctMatrix bounds the inverse dct matrix so that no pixel has a
 * value greater than 255 (4095) or less than 0.
 */
void
BoundIDctMatrix (int *matrix, int Bound)
{
  int *mptr;

  for (mptr = matrix; mptr < matrix + DCTSIZE2; mptr++)
    {
      if (*mptr < 0)
	*mptr = 0;
      else if (*mptr > Bound)
	*mptr = Bound;
    }
}



void
WriteOneBlock (int *store, unsigned char *out_buf, int width, int height, int voffs,
	       int hoffs)
{
  int i, e;


  /* Find vertical buffer offs. */
  for (i = voffs; i < voffs + DCTSIZE; i++)
    {
      if (i < height)
	{
	  int diff;
	  diff = width * i;
	  for (e = hoffs; e < hoffs + DCTSIZE; e++)
	    {
	      if (e < width)
		out_buf[diff + e] = (unsigned char) (*(store++));
	      else
		break;
	    }
	}
      else
	break;
    }


}

/*
 * WriteBlock() writes an array of data in the integer array pointed to
 * by store out to the driver specified by the IOB.  The integer array is
 * stored in row-major form, that is, the first row of (8) elements, the
 * second row of (8) elements....
 * ONLY for MCU 1:1:1
 */
void
WriteBlock (int *store)
{
  int voffs, hoffs;

  /*
   * Get vertical offsets
   */
  voffs = p_out_vpos * DCTSIZE;
  hoffs = p_out_hpos * DCTSIZE;

  /*
   * Writing block
   */
  WriteOneBlock (store, p_out_buf, DecodeInfo_image_width,
		 DecodeInfo_image_height, voffs, hoffs);

  /*
   *  Add positions
   */
  p_out_hpos++;
  p_out_vpos++;

  if (p_out_hpos < DecodeInfo_MCUWidth)
    p_out_vpos--;
  else
    p_out_hpos = 0;		/* If at end of image (width) */
}

/*
 *  4:1:1
 */
void
Write4Blocks (int *store1, int *store2, int *store3, int *store4)
{
  int voffs, hoffs;

  /*
   * OX
   * XX
   */
  voffs = p_out_vpos * DCTSIZE;
  hoffs = p_out_hpos * DCTSIZE;
  WriteOneBlock (store1, p_out_buf, DecodeInfo_image_width,
		 DecodeInfo_image_height, voffs, hoffs);

  /*
   * XO
   * XX
   */
  hoffs += DCTSIZE;
  WriteOneBlock (store2, p_out_buf, DecodeInfo_image_width,
		 DecodeInfo_image_height, voffs, hoffs);

  /*
   * XX
   * OX
   */
  voffs += DCTSIZE;
  hoffs -= DCTSIZE;
  WriteOneBlock (store3, p_out_buf, DecodeInfo_image_width,
		 DecodeInfo_image_height, voffs, hoffs);


  /*
   * XX
   * XO
   */
  hoffs += DCTSIZE;
  WriteOneBlock (store4, p_out_buf, DecodeInfo_image_width,
		 DecodeInfo_image_height, voffs, hoffs);


  /*
   *  Add positions
   */
  p_out_hpos = p_out_hpos + 2;
  p_out_vpos = p_out_vpos + 2;


  if (p_out_hpos < DecodeInfo_MCUWidth)
    p_out_vpos = p_out_vpos - 2;
  else
    p_out_hpos = 0;		/* If at end of image (width) */
}


/*
 *  Transform from Yuv into RGB
 */
void
YuvToRgb (int rgb_buf[RGB_NUM][DCTSIZE2], int *y_buf, int *u_buf, int *v_buf)
{
  int r, g, b;
  int y, u, v;
  int i;


  for (i = 0; i < DCTSIZE2; i++)
    {
      y = y_buf[i];
      u = u_buf[i] - 128;
      v = v_buf[i] - 128;

      r = (y * 256 + v * 359 + 128) >> 8;
      g = (y * 256 - u * 88 - v * 182 + 128) >> 8;
      b = (y * 256 + u * 454 + 128) >> 8;

      if (r < 0)
	r = 0;
      else if (r > 255)
	r = 255;

      if (g < 0)
	g = 0;
      else if (g > 255)
	g = 255;

      if (b < 0)
	b = 0;
      else if (b > 255)
	b = 255;

      rgb_buf[0][i] = r;
      rgb_buf[1][i] = g;
      rgb_buf[2][i] = b;

    }
}

/*
 * Decode one block
 */
void
decode_block (int comp_no, int *out_buf, int *HuffBuff)
{
  int QuantBuff[DCTSIZE2];
  unsigned int *p_quant_tbl;

  DecodeHuffMCU (HuffBuff, comp_no);

  IZigzagMatrix (HuffBuff, QuantBuff);

  p_quant_tbl =
    DecodeInfo_quant_tbl_quantval[(int)
				  DecodeInfo_comps_info_quant_tbl_no
				  [comp_no]];
  IQuantize (QuantBuff, p_quant_tbl);

  ChenIDct (QuantBuff, out_buf);

  PostshiftIDctMatrix (out_buf, IDCT_SHIFT);

  BoundIDctMatrix (out_buf, IDCT_BOUNT);

}

void
decode_start ()
{
  int i, j;
  int CurrentMCU = 0;
  int HuffBuff[NUM_COMPONENT][DCTSIZE2];
  int IDCTBuff[6][DCTSIZE2];
  int rgb_buf[4][RGB_NUM][DCTSIZE2];

  /* Read buffer */

  /*
   * Initial value of DC element is 0
   */
  for (i = 0; i < NUM_COMPONENT; i++)
    {
      HuffBuff[i][0] = 0;
    }

  /*
   * Set the size of image to output buffer
   */
  OutData_image_width = DecodeInfo_image_width;
  OutData_image_height = DecodeInfo_image_height;

  /*
   * Initialize output buffer
   */
  for (i = 0; i < RGB_NUM; i++)
    {
      OutData_comp_vpos[i] = 0;
      OutData_comp_hpos[i] = 0;
    }


  if (DecodeInfo_smp_fact == SF1_1_1)
    {
      /*
       * 1_1_1
       */
      while (CurrentMCU < DecodeInfo_NumMCU)
	{

	  for (i = 0; i < NUM_COMPONENT; i++)
	    decode_block (i, IDCTBuff[i], HuffBuff[i]);

	  YuvToRgb (rgb_buf[0], IDCTBuff[0], IDCTBuff[1], IDCTBuff[2]);
	  /*
	   * Writing
	   */
	  for (i = 0; i < RGB_NUM; i++)
	    {
	      p_out_vpos = OutData_comp_vpos[i];
	      p_out_hpos = OutData_comp_hpos[i];
	      for (j = 0; j < BMP_OUT_SIZE; j++)
		{
		  p_out_buf[j] = OutData_comp_buf[i][j];
		}
	      WriteBlock (rgb_buf[0][i]);
	    }
	  CurrentMCU++;
	}

    }
  else
    {
      /*
       * 4_1_1
       */
      while (CurrentMCU < DecodeInfo_NumMCU)
	{
	  /*
	   * Decode Y element
	   * Decoding Y, U and V elements should be sequentially conducted for the use of Huffman table
	   */

	  for (i = 0; i < 4; i++)
	    {
	      decode_block (0, IDCTBuff[i], HuffBuff[0]);
	    }

	  /* Decode U element */
	  decode_block (1, IDCTBuff[4], HuffBuff[1]);

	  /* Decode V element */
	  decode_block (2, IDCTBuff[5], HuffBuff[2]);


	  /* Transform from Yuv into RGB */

	  for (i = 0; i < 4; i++)
	    {
	      YuvToRgb (rgb_buf[i], IDCTBuff[i], IDCTBuff[4], IDCTBuff[5]);
	    }


	  for (i = 0; i < RGB_NUM; i++)
	    {
	      p_out_vpos = OutData_comp_vpos[i];
	      p_out_hpos = OutData_comp_hpos[i];
	      for (j = 0; j < BMP_OUT_SIZE; j++)
		{
		  p_out_buf[j] = OutData_comp_buf[i][j];
		}
	      Write4Blocks (rgb_buf[0][i],
			    rgb_buf[1][i], rgb_buf[2][i], rgb_buf[3][i]);
	    }

	  CurrentMCU += 4;
	}
    }
}
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
/*
 * Read the header information from buffer in JFIF format and begin decoding
 *
 *  @(#) $Id: jfif_read.c,v 1.2 2003/07/18 10:19:21 honda Exp $ 
 */

int *p_xhtbl_bits;
int p_dhtbl_ml;
int p_dhtbl_maxcode[36], p_dhtbl_mincode[36], p_dhtbl_valptr[36];

/*
 * Initialize JPEG_DECODE_INFO after reading markers
 */
void
jpeg_init_decompress ()
{
  int i;
  /*
   * Get MCU number
   */
  DecodeInfo_MCUHeight = (DecodeInfo_image_height - 1) / 8 + 1;
  DecodeInfo_MCUWidth = (DecodeInfo_image_width - 1) / 8 + 1;
  DecodeInfo_NumMCU = DecodeInfo_MCUHeight * DecodeInfo_MCUWidth;

  /*
   *  Create Huffman Table for decoding
   */
  p_xhtbl_bits = DecodeInfo_dc_xhuff_tbl_bits[0];
  huff_make_dhuff_tb ();
  DecodeInfo_dc_dhuff_tbl_ml[0] = p_dhtbl_ml;
  for (i = 0; i < 36; i++)
    {
      DecodeInfo_dc_dhuff_tbl_maxcode[0][i] = p_dhtbl_maxcode[i];
      DecodeInfo_dc_dhuff_tbl_mincode[0][i] = p_dhtbl_mincode[i];
      DecodeInfo_dc_dhuff_tbl_valptr[0][i] = p_dhtbl_valptr[i];
    }

  p_xhtbl_bits = DecodeInfo_dc_xhuff_tbl_bits[1];
  huff_make_dhuff_tb ();
  DecodeInfo_dc_dhuff_tbl_ml[1] = p_dhtbl_ml;
  for (i = 0; i < 36; i++)
    {
      DecodeInfo_dc_dhuff_tbl_maxcode[1][i] = p_dhtbl_maxcode[i];
      DecodeInfo_dc_dhuff_tbl_mincode[1][i] = p_dhtbl_mincode[i];
      DecodeInfo_dc_dhuff_tbl_valptr[1][i] = p_dhtbl_valptr[i];
    }

  p_xhtbl_bits = DecodeInfo_ac_xhuff_tbl_bits[0];
  huff_make_dhuff_tb ();
  DecodeInfo_ac_dhuff_tbl_ml[0] = p_dhtbl_ml;
  for (i = 0; i < 36; i++)
    {
      DecodeInfo_ac_dhuff_tbl_maxcode[0][i] = p_dhtbl_maxcode[i];
      DecodeInfo_ac_dhuff_tbl_mincode[0][i] = p_dhtbl_mincode[i];
      DecodeInfo_ac_dhuff_tbl_valptr[0][i] = p_dhtbl_valptr[i];
    }

  p_xhtbl_bits = DecodeInfo_ac_xhuff_tbl_bits[1];
  huff_make_dhuff_tb ();
  DecodeInfo_ac_dhuff_tbl_ml[1] = p_dhtbl_ml;
  for (i = 0; i < 36; i++)
    {
      DecodeInfo_ac_dhuff_tbl_maxcode[1][i] = p_dhtbl_maxcode[i];
      DecodeInfo_ac_dhuff_tbl_mincode[1][i] = p_dhtbl_mincode[i];
      DecodeInfo_ac_dhuff_tbl_valptr[1][i] = p_dhtbl_valptr[i];
    }
}



void
jpeg_read (unsigned char *read_buf)
{
  /*
   *  Read markers
   */
  read_markers (read_buf);


  /*
   * Initialize the information used for decoding
   * 
   */
  jpeg_init_decompress ();

  /*
   *  Start decoding
   */
  decode_start ();
}
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 *  Huffman decoding module
 *
 *  @(#) $Id: huffman.c,v 1.2 2003/07/18 10:19:21 honda Exp $
 */

/*************************************************************
Copyright (C) 1990, 1991, 1993 Andy C. Hung, all rights reserved.
PUBLIC DOMAIN LICENSE: Stanford University Portable Video Research
Group. If you use this software, you agree to the following: This
program package is purely experimental, and is licensed "as is".
Permission is granted to use, modify, and distribute this program
without charge for any purpose, provided this license/ disclaimer
notice appears in the copies.  No warranty or maintenance is given,
either expressed or implied.  In no event shall the author(s) be
liable to you or a third party for any special, incidental,
consequential, or other damages, arising out of the use or inability
to use the program for any purpose (or the loss of data), even if we
have been advised of such possibilities.  Any public reference or
advertisement of this source code should refer to it as the Portable
Video Research Group (PVRG) code, and not by any author(s) (or
Stanford University) name.
*************************************************************/
/*
************************************************************
huffman.c

This file represents the core Huffman routines, most of them
implemented with the JPEG reference. These routines are not very fast
and can be improved, but comprise very little of software run-time.

************************************************************
*/

/* Used for sign extensions. */
const static int extend_mask[20] = {
  0xFFFFFFFE, 0xFFFFFFFC, 0xFFFFFFF8, 0xFFFFFFF0, 0xFFFFFFE0, 0xFFFFFFC0,
  0xFFFFFF80, 0xFFFFFF00, 0xFFFFFE00, 0xFFFFFC00, 0xFFFFF800, 0xFFFFF000,
  0xFFFFE000, 0xFFFFC000, 0xFFFF8000, 0xFFFF0000, 0xFFFE0000, 0xFFFC0000,
  0xFFF80000, 0xFFF00000
};


/* Masks */
const int bit_set_mask[32] = {	/* This is 2^i at ith position */
  0x00000001, 0x00000002, 0x00000004, 0x00000008,
  0x00000010, 0x00000020, 0x00000040, 0x00000080,
  0x00000100, 0x00000200, 0x00000400, 0x00000800,
  0x00001000, 0x00002000, 0x00004000, 0x00008000,
  0x00010000, 0x00020000, 0x00040000, 0x00080000,
  0x00100000, 0x00200000, 0x00400000, 0x00800000,
  0x01000000, 0x02000000, 0x04000000, 0x08000000,
  0x10000000, 0x20000000, 0x40000000, 0x80000000
};

const int lmask[32] = {		/* This is 2^{i+1}-1 */
  0x00000001, 0x00000003, 0x00000007, 0x0000000f,
  0x0000001f, 0x0000003f, 0x0000007f, 0x000000ff,
  0x000001ff, 0x000003ff, 0x000007ff, 0x00000fff,
  0x00001fff, 0x00003fff, 0x00007fff, 0x0000ffff,
  0x0001ffff, 0x0003ffff, 0x0007ffff, 0x000fffff,
  0x001fffff, 0x003fffff, 0x007fffff, 0x00ffffff,
  0x01ffffff, 0x03ffffff, 0x07ffffff, 0x0fffffff,
  0x1fffffff, 0x3fffffff, 0x7fffffff, 0xffffffff
};

/* Read buffer */
static unsigned int current_read_byte;
static int read_position = -1;

int *Xhuff_huffval;
int Dhuff_ml;
int *Dhuff_maxcode;
int *Dhuff_mincode;
int *Dhuff_valptr;
/*
 * pgetc() gets a character onto the stream but it checks to see
 * if there are any marker conflicts.
 */
static int
pgetc ()
{
  int temp;

  if ((temp = *CurHuffReadBuf++) == MARKER_MARKER)
    {				/* If MARKER then */
      if ((temp = *CurHuffReadBuf++))
	{			/* if next is not 0xff, then marker */
	  main_result++;
	}
      else
	{
	  return (MARKER_MARKER);
	}
    }
  return (temp);
}


/*
 * buf_getb() gets a bit from the read stream.
 */
int
buf_getb ()
{
  if (read_position < 0)
    {
      current_read_byte = pgetc ();
      read_position = 7;
    }

  if (current_read_byte & bit_set_mask[read_position--])
    {
      return (1);
    }
  return (0);
}


/*
 * megetv() gets n bits from the read stream and returns it.
 *
 */
int
buf_getv (int n)
{
  int p, rv;

  n--;
  p = n - read_position;
  while (p > 0)
    {
      if (read_position > 23)
	{			/* If byte buffer contains almost entire word */
	  rv = (current_read_byte << p);	/* Manipulate buffer */
	  current_read_byte = pgetc ();	/* Change read bytes */

	  rv |= (current_read_byte >> (8 - p));
	  read_position = 7 - p;
	  return (rv & lmask[n]);
	  /* Can return pending residual val */
	}
      current_read_byte = (current_read_byte << 8) | pgetc ();
      read_position += 8;	/* else shift in new information */
      p -= 8;
    }

  if (!p)
    {				/* If position is zero */
      read_position = -1;
      /* Can return current byte */
      return (current_read_byte & lmask[n]);
    }

  p = -p;
  /* Else reverse position and shift */
  read_position = p - 1;
  return ((current_read_byte >> p) & lmask[n]);
}



/*
 * Create Table for decoding
 */
void
huff_make_dhuff_tb ()
{
  int i, j, p, code, size, l, lastp;
  int huffsize[257];
  int huffcode[257];

  /*
   * Get the size
   */
  for (p = 0, i = 1; i < 17; i++)
    {
      for (j = 1; j <= p_xhtbl_bits[i]; j++)
	{
	  huffsize[p++] = i;
	}
    }

  huffsize[p] = 0;
  lastp = p;

  p = 0;
  code = 0;
  size = huffsize[0];
  while (1)
    {
      do
	{
	  huffcode[p++] = code++;
	}
      while ((huffsize[p] == size) && (p < 257));
      /* Overflow Detection */
      if (!huffsize[p])
	break;			/* All finished. */
      do
	{
	  /* Shift next code to expand prefix. */
	  code <<= 1;
	  size++;
	}
      while (huffsize[p] != size);

    }

  for (p_dhtbl_ml = 1, p = 0, l = 1; l <= 16; l++)
    {
      if (p_xhtbl_bits[l] == 0)
	{
	  p_dhtbl_maxcode[l] = -1;	/* Watch out JPEG is wrong here */
	}
      else
	{			/* We use -1 to indicate skipping. */
	  p_dhtbl_valptr[l] = p;
	  p_dhtbl_mincode[l] = huffcode[p];
	  p += p_xhtbl_bits[l] - 1;
	  p_dhtbl_maxcode[l] = huffcode[p];
	  p_dhtbl_ml = l;
	  p++;
	}
    }
  p_dhtbl_maxcode[p_dhtbl_ml] += 1;
}


/*
 *  
 */
int
DecodeHuffman ()
{
  int code, l, p;

  code = buf_getb ();
  for (l = 1; code > Dhuff_maxcode[l]; l++)
    {
      code = (code << 1) + buf_getb ();
    }

  if (code < Dhuff_maxcode[Dhuff_ml])
    {
      p = Dhuff_valptr[l] + code - Dhuff_mincode[l];
      return (Xhuff_huffval[p]);
    }
  else
    {
      main_result++;
    }
	return (-1);
}


/*
 * Decode one MCU
 */
void
DecodeHuffMCU (int *out_buf, int num_cmp)
{
  int s, diff, tbl_no;
  int *mptr, k, n, r;

  /*
   *  Decode DC
   */
  tbl_no = DecodeInfo_comps_info_dc_tbl_no[num_cmp];
  Xhuff_huffval = DecodeInfo_dc_xhuff_tbl_huffval[tbl_no];
  Dhuff_ml = DecodeInfo_dc_dhuff_tbl_ml[tbl_no];
  Dhuff_maxcode = DecodeInfo_dc_dhuff_tbl_maxcode[tbl_no];
  Dhuff_mincode = DecodeInfo_dc_dhuff_tbl_mincode[tbl_no];
  Dhuff_valptr = DecodeInfo_dc_dhuff_tbl_valptr[tbl_no];
  s = DecodeHuffman ();


  if (s)
    {
      diff = buf_getv (s);
      s--;
      if ((diff & bit_set_mask[s]) == 0)
	{
	  diff |= extend_mask[s];
	  diff++;
	}

      diff += *out_buf;		/* Change the last DC */
      *out_buf = diff;
    }

  /*
   * Decode AC
   */
  /* Set all values to zero */
  for (mptr = out_buf + 1; mptr < out_buf + DCTSIZE2; mptr++)
    {
      *mptr = 0;
    }

  for (k = 1; k < DCTSIZE2;)
    {				/* JPEG Mistake */
      Xhuff_huffval = DecodeInfo_dc_xhuff_tbl_huffval[tbl_no];
      Dhuff_ml = DecodeInfo_ac_dhuff_tbl_ml[tbl_no];
      Dhuff_maxcode = DecodeInfo_ac_dhuff_tbl_maxcode[tbl_no];
      Dhuff_mincode = DecodeInfo_ac_dhuff_tbl_mincode[tbl_no];
      Dhuff_valptr = DecodeInfo_ac_dhuff_tbl_valptr[tbl_no];
      r = DecodeHuffman ();


      s = r & 0xf;		/* Find significant bits */
      n = (r >> 4) & 0xf;	/* n = run-length */

      if (s)
	{
	  if ((k += n) >= DCTSIZE2)	/* JPEG Mistake */
	    {
	      break;
	    }
	  out_buf[k] = buf_getv (s);	/* Get s bits */
	  s--;			/* Align s */
	  if ((out_buf[k] & bit_set_mask[s]) == 0)
	    {			/* Also (1 << s) */
	      out_buf[k] |= extend_mask[s];	/* Also  (-1 << s) + 1 */
	      out_buf[k]++;	/* Increment 2's c */
	    }
	  k++;			/* Goto next element */
	}
      else if (n == 15)		/* Zero run length code extnd */
	{
	  k += 16;
	}
      else
	{
	  break;
	}

    }
}
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims  any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */

/*
+--------------------------------------------------------------------------+
| * Test Vector (added for CHStone)                                        |
|     hana : input data                                                    |
+--------------------------------------------------------------------------+
*/
#define JPEGSIZE 7506
const unsigned char hana[JPEGSIZE] = {
  255, 216, 255, 224, 0, 16, 74, 70, 73, 70, 0, 1, 1, 1, 0, 96, 0, 96, 0, 0,
  255, 225, 0, 22, 69, 120, 105, 102, 0, 0, 73, 73, 42, 0, 8, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 255, 219, 0, 67, 0, 8,
  6, 6, 7, 6, 5, 8, 7, 7, 7, 9, 9, 8, 10, 12, 20, 13, 12, 11, 11, 12, 25, 18,
    19, 15, 20, 29, 26, 31, 30, 29,
  26, 28, 28, 32, 36, 46, 39, 32, 34, 44, 35, 28, 28, 40, 55, 41, 44, 48, 49,
    52, 52, 52, 31, 39, 57, 61, 56,
  50, 60, 46, 51, 52, 50, 255, 219, 0, 67, 1, 9, 9, 9, 12, 11, 12, 24, 13, 13,
    24, 50, 33, 28, 33, 50, 50, 50,
  50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50,
    50, 50, 50, 50, 50, 50, 50, 50,
  50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50, 50,
    50, 255, 192, 0, 17, 8, 0, 113,
  0, 150, 3, 1, 34, 0, 2, 17, 1, 3, 17, 1, 255, 196, 0, 31, 0, 0, 1, 5, 1, 1,
    1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 255, 196, 0, 181, 16, 0, 2, 1, 3, 3,
    2, 4, 3, 5, 5, 4, 4, 0, 0, 1, 125,
  1, 2, 3, 0, 4, 17, 5, 18, 33, 49, 65, 6, 19, 81, 97, 7, 34, 113, 20, 50,
    129, 145, 161, 8, 35, 66, 177, 193,
  21, 82, 209, 240, 36, 51, 98, 114, 130, 9, 10, 22, 23, 24, 25, 26, 37, 38,
    39, 40, 41, 42, 52, 53, 54, 55,
  56, 57, 58, 67, 68, 69, 70, 71, 72, 73, 74, 83, 84, 85, 86, 87, 88, 89, 90,
    99, 100, 101, 102, 103, 104, 105,
  106, 115, 116, 117, 118, 119, 120, 121, 122, 131, 132, 133, 134, 135, 136,
    137, 138, 146, 147, 148, 149, 150,
  151, 152, 153, 154, 162, 163, 164, 165, 166, 167, 168, 169, 170, 178, 179,
    180, 181, 182, 183, 184, 185, 186,
  194, 195, 196, 197, 198, 199, 200, 201, 202, 210, 211, 212, 213, 214, 215,
    216, 217, 218, 225, 226, 227, 228,
  229, 230, 231, 232, 233, 234, 241, 242, 243, 244, 245, 246, 247, 248, 249,
    250, 255, 196, 0, 31, 1, 0, 3, 1,
  1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    255, 196, 0, 181, 17, 0, 2, 1,
  2, 4, 4, 3, 4, 7, 5, 4, 4, 0, 1, 2, 119, 0, 1, 2, 3, 17, 4, 5, 33, 49, 6,
    18, 65, 81, 7, 97, 113, 19, 34, 50,
  129, 8, 20, 66, 145, 161, 177, 193, 9, 35, 51, 82, 240, 21, 98, 114, 209,
    10, 22, 36, 52, 225, 37, 241, 23,
  24, 25, 26, 38, 39, 40, 41, 42, 53, 54, 55, 56, 57, 58, 67, 68, 69, 70, 71,
    72, 73, 74, 83, 84, 85, 86, 87,
  88, 89, 90, 99, 100, 101, 102, 103, 104, 105, 106, 115, 116, 117, 118, 119,
    120, 121, 122, 130, 131, 132,
  133, 134, 135, 136, 137, 138, 146, 147, 148, 149, 150, 151, 152, 153, 154,
    162, 163, 164, 165, 166, 167, 168,
  169, 170, 178, 179, 180, 181, 182, 183, 184, 185, 186, 194, 195, 196, 197,
    198, 199, 200, 201, 202, 210, 211,
  212, 213, 214, 215, 216, 217, 218, 226, 227, 228, 229, 230, 231, 232, 233,
    234, 242, 243, 244, 245, 246, 247,
  248, 249, 250, 255, 218, 0, 12, 3, 1, 0, 2, 17, 3, 17, 0, 63, 0, 211, 181,
    213, 46, 245, 205, 122, 59, 43,
  134, 150, 206, 198, 214, 18, 242, 74, 232, 84, 74, 221, 48, 27, 243, 171,
    250, 217, 139, 195, 254, 28, 184,
  184, 177, 89, 110, 18, 83, 186, 60, 49, 102, 231, 251, 190, 162, 179, 244,
    111, 16, 88, 120, 143, 72, 187,
  183, 213, 102, 142, 18, 37, 48, 152, 25, 128, 145, 72, 56, 207, 245, 174,
    150, 218, 210, 37, 182, 180, 182,
  134, 97, 60, 48, 161, 81, 191, 146, 107, 101, 121, 78, 253, 59, 139, 161,
    192, 248, 111, 226, 47, 219, 94,
  223, 78, 189, 181, 153, 110, 139, 20, 50, 170, 228, 168, 30, 189, 197, 111,
    104, 254, 35, 180, 187, 212, 103,
  176, 186, 185, 158, 221, 210, 109, 246, 211, 59, 225, 102, 94, 56, 30, 249,
    237, 83, 233, 82, 232, 247, 62,
  33, 212, 161, 120, 227, 75, 197, 144, 194, 178, 121, 124, 178, 140, 103,
    159, 194, 157, 109, 107, 117, 6,
  185, 119, 12, 246, 214, 195, 75, 80, 173, 3, 50, 135, 46, 255, 0, 211, 154,
    210, 13, 78, 58, 234, 45, 81,
  103, 197, 186, 86, 159, 168, 218, 186, 106, 22, 142, 241, 238, 27, 25, 24,
    134, 221, 248, 87, 148, 143, 5,
  73, 117, 121, 117, 21, 173, 196, 144, 21, 57, 138, 57, 241, 151, 95, 194,
    189, 43, 95, 186, 142, 241, 124,
  139, 155, 187, 136, 102, 181, 147, 114, 73, 110, 185, 137, 223, 251, 173,
    239, 237, 85, 102, 177, 125, 94,
  27, 103, 151, 100, 46, 153, 6, 68, 110, 115, 219, 21, 92, 144, 154, 188,
    144, 236, 120, 254, 171, 162, 220,
  105, 202, 126, 219, 110, 209, 149, 59, 71, 60, 31, 198, 160, 210, 174, 211,
    72, 214, 44, 238, 246, 150, 242,
  88, 51, 1, 222, 189, 106, 251, 194, 18, 221, 232, 55, 75, 121, 168, 44, 174,
    145, 150, 86, 219, 233, 94, 112,
  250, 4, 114, 232, 49, 234, 113, 221, 3, 113, 35, 109, 88, 8, 235, 206, 0,
    21, 201, 58, 14, 19, 92, 158, 162,
  189, 153, 235, 246, 186, 197, 158, 185, 165, 11, 139, 139, 80, 241, 237, 12,
    16, 174, 120, 174, 35, 196, 73,
  162, 234, 26, 132, 38, 210, 209, 98, 40, 114, 204, 171, 128, 125, 171, 173,
    248, 125, 25, 135, 195, 201, 13,
  236, 97, 102, 143, 48, 58, 14, 120, 207, 7, 242, 197, 115, 94, 37, 240, 197,
    254, 147, 44, 183, 81, 254, 242,
  211, 37, 203, 47, 85, 21, 120, 151, 41, 82, 247, 80, 159, 115, 149, 212,
    111, 55, 93, 139, 88, 23, 247, 107,
  247, 136, 236, 43, 54, 95, 41, 39, 44, 163, 128, 43, 82, 217, 34, 158, 221,
    238, 124, 206, 115, 208, 114,
  106, 173, 197, 180, 108, 75, 195, 150, 143, 185, 175, 42, 45, 37, 100, 13,
    244, 49, 230, 51, 72, 12, 187, 88,
  198, 14, 11, 1, 198, 107, 82, 251, 72, 212, 116, 205, 30, 27, 219, 187, 66,
    176, 77, 128, 15, 92, 30, 217,
  174, 131, 192, 250, 134, 148, 151, 119, 122, 86, 166, 136, 208, 204, 161,
    215, 119, 99, 233, 252, 141, 122,
  150, 163, 225, 251, 61, 107, 195, 255, 0, 103, 50, 239, 131, 134, 10, 56,
    35, 28, 255, 0, 74, 244, 168, 211,
  82, 133, 208, 214, 135, 206, 126, 120, 109, 160, 166, 50, 123, 138, 209,
    213, 44, 151, 236, 113, 178, 129,
  201, 21, 208, 248, 163, 195, 208, 88, 220, 34, 164, 91, 34, 207, 222, 221,
    222, 163, 125, 55, 237, 150, 73,
  26, 54, 236, 87, 13, 121, 56, 84, 180, 186, 15, 115, 140, 145, 12, 48, 130,
    15, 81, 73, 22, 208, 6, 123, 227,
  53, 210, 94, 105, 43, 13, 190, 199, 199, 78, 245, 146, 250, 116, 104, 9, 18,
    18, 125, 59, 83, 133, 69, 36,
  28, 172, 209, 17, 218, 155, 100, 35, 175, 67, 197, 21, 141, 243, 69, 242,
    238, 56, 237, 205, 21, 175, 50, 42,
  230, 238, 183, 119, 246, 93, 95, 126, 114, 92, 249, 132, 175, 112, 123, 215,
    75, 163, 248, 229, 108, 180,
  139, 137, 143, 153, 44, 232, 193, 81, 28, 224, 47, 189, 113, 23, 146, 253,
    171, 200, 103, 96, 100, 84, 216,
  205, 219, 218, 153, 46, 157, 44, 1, 209, 159, 113, 56, 198, 222, 153, 61, 7,
    233, 90, 66, 164, 249, 21, 186,
  25, 167, 99, 211, 244, 239, 28, 233, 186, 21, 153, 186, 185, 133, 228, 188,
    186, 186, 121, 29, 17, 115, 177,
  24, 231, 32, 255, 0, 78, 245, 217, 91, 172, 154, 197, 186, 186, 70, 235, 99,
    116, 155, 227, 147, 24, 32, 158,
  121, 231, 142, 213, 226, 151, 122, 108, 242, 201, 12, 234, 209, 152, 138, 8,
    202, 19, 201, 32, 117, 253, 69,
  119, 127, 15, 188, 68, 182, 58, 29, 237, 158, 161, 121, 112, 36, 182, 153,
    124, 136, 151, 230, 202, 145, 156,
  14, 51, 212, 31, 110, 149, 209, 66, 164, 146, 73, 171, 92, 23, 67, 160, 159,
    68, 158, 210, 11, 219, 169, 47,
  217, 210, 68, 193, 135, 169, 86, 31, 197, 245, 175, 55, 159, 84, 212, 110,
    46, 124, 139, 57, 159, 204, 64,
  91, 104, 98, 54, 125, 107, 210, 96, 212, 226, 157, 174, 110, 52, 107, 57,
    29, 165, 57, 127, 61, 142, 26, 77,
  187, 136, 207, 59, 127, 250, 245, 231, 237, 170, 67, 62, 185, 246, 125, 82,
    63, 179, 77, 35, 126, 245, 35, 4,
  54, 63, 186, 79, 165, 92, 167, 40, 91, 165, 202, 126, 71, 79, 101, 172, 219,
    143, 5, 180, 23, 23, 101, 175,
  190, 206, 193, 135, 241, 22, 198, 42, 111, 9, 120, 115, 77, 213, 124, 43,
    165, 201, 48, 5, 212, 22, 36, 118,
  98, 77, 100, 234, 218, 205, 150, 143, 60, 182, 22, 154, 122, 236, 191, 135,
    203, 87, 82, 62, 83, 211, 38,
  181, 252, 12, 117, 23, 210, 172, 161, 180, 26, 99, 67, 4, 139, 5, 203, 121,
    164, 186, 3, 206, 64, 198, 9,
  193, 245, 235, 73, 78, 243, 249, 19, 212, 181, 168, 88, 91, 104, 26, 221,
    165, 236, 23, 83, 24, 154, 63, 45,
  226, 83, 149, 44, 59, 154, 216, 176, 213, 44, 181, 111, 181, 91, 249, 194,
    79, 44, 98, 68, 199, 64, 104, 107,
  18, 39, 184, 89, 164, 129, 237, 22, 70, 141, 21, 112, 74, 56, 60, 134, 244,
    60, 244, 60, 243, 92, 198, 150,
  83, 195, 158, 40, 100, 191, 131, 236, 118, 218, 156, 159, 186, 144, 186,
    249, 100, 129, 211, 57, 227, 60,
  117, 245, 174, 136, 175, 49, 154, 118, 154, 61, 142, 132, 233, 29, 148, 112,
    71, 105, 42, 150, 111, 52, 124,
  213, 195, 234, 218, 114, 217, 95, 78, 109, 241, 246, 121, 88, 178, 241, 192,
    207, 92, 123, 87, 170, 107, 26,
  0, 214, 108, 214, 22, 59, 21, 88, 121, 108, 189, 121, 201, 193, 7, 233, 92,
    15, 139, 236, 181, 56, 109, 237,
  99, 188, 129, 109, 218, 32, 121, 83, 144, 71, 225, 88, 87, 167, 205, 11, 90,
    246, 236, 47, 67, 131, 155, 70,
  153, 117, 4, 150, 219, 63, 51, 125, 225, 252, 39, 235, 93, 48, 241, 142,
    187, 167, 232, 178, 91, 74, 17, 66,
  252, 190, 96, 24, 56, 169, 252, 9, 255, 0, 19, 33, 119, 166, 178, 150, 114,
    68, 136, 199, 248, 127, 206, 43,
  165, 241, 151, 135, 45, 37, 209, 35, 19, 72, 182, 236, 152, 47, 32, 226,
    178, 163, 31, 114, 235, 113, 221,
  216, 243, 153, 165, 125, 98, 201, 164, 55, 15, 36, 160, 103, 107, 30, 149,
    83, 66, 189, 189, 130, 227, 100,
  138, 74, 131, 134, 172, 251, 67, 117, 30, 173, 36, 122, 106, 203, 117, 28,
    103, 254, 89, 174, 114, 43, 209,
  60, 49, 99, 99, 58, 23, 212, 173, 103, 136, 191, 82, 80, 129, 143, 90, 225,
    116, 42, 73, 184, 191, 188, 46,
  100, 120, 149, 9, 178, 73, 98, 254, 44, 10, 226, 165, 73, 50, 25, 179, 248,
    215, 184, 107, 126, 21, 179, 185,
  209, 230, 77, 45, 36, 146, 230, 52, 18, 68, 172, 126, 87, 31, 90, 242, 233,
    101, 150, 221, 93, 46, 108, 218,
  50, 185, 12, 172, 57, 21, 10, 14, 154, 177, 86, 232, 206, 118, 102, 0, 12,
    81, 90, 66, 210, 43, 147, 230,
  198, 7, 61, 168, 163, 158, 40, 155, 6, 153, 101, 111, 168, 106, 214, 150,
    147, 204, 109, 237, 167, 109, 175,
  39, 247, 115, 211, 147, 239, 138, 244, 189, 59, 65, 134, 29, 70, 243, 76,
    145, 82, 114, 210, 67, 111, 230,
  28, 103, 62, 75, 190, 71, 215, 143, 196, 215, 155, 201, 53, 231, 135, 111,
    38, 211, 175, 226, 6, 38, 1, 154,
  55, 25, 220, 164, 231, 131, 249, 215, 174, 248, 78, 127, 14, 107, 218, 96,
    22, 176, 91, 196, 35, 97, 187, 17,
  237, 120, 219, 24, 4, 145, 206, 120, 224, 231, 156, 123, 87, 167, 135, 138,
    107, 70, 46, 186, 152, 122, 255,
  0, 134, 245, 15, 15, 67, 52, 226, 24, 110, 52, 201, 88, 21, 98, 114, 209,
    103, 28, 227, 183, 165, 115, 154,
  22, 141, 46, 179, 226, 89, 45, 237, 165, 100, 142, 50, 37, 147, 203, 108,
    110, 80, 236, 8, 7, 241, 3, 191,
  90, 244, 45, 95, 90, 105, 181, 87, 240, 181, 218, 173, 228, 151, 192, 172,
    50, 253, 193, 20, 92, 228, 191,
  185, 35, 0, 142, 254, 131, 21, 195, 197, 170, 219, 248, 51, 199, 51, 186, 6,
    22, 232, 100, 132, 128, 219,
  142, 221, 234, 122, 254, 21, 53, 121, 95, 42, 217, 92, 62, 23, 161, 222,
    120, 125, 101, 177, 214, 47, 150,
  222, 226, 213, 44, 99, 138, 48, 96, 97, 195, 179, 100, 242, 113, 195, 1,
    143, 206, 171, 235, 99, 195, 58,
  215, 137, 180, 251, 107, 168, 85, 138, 249, 169, 43, 69, 38, 26, 55, 96, 2,
    0, 195, 177, 96, 220, 31, 239, 3,
  92, 206, 139, 227, 27, 11, 40, 124, 68, 186, 133, 147, 27, 203, 135, 154,
    86, 70, 92, 146, 8, 56, 95, 192, 1,
  86, 252, 27, 225, 109, 42, 255, 0, 194, 80, 193, 230, 69, 45, 208, 218, 46,
    93, 6, 24, 59, 97, 213, 91, 254,
  2, 66, 131, 234, 167, 222, 171, 154, 85, 35, 203, 31, 95, 95, 32, 232, 96,
    120, 214, 59, 29, 51, 196, 246,
  250, 93, 133, 157, 196, 46, 152, 107, 137, 103, 46, 124, 206, 56, 219, 187,
    168, 247, 24, 21, 141, 225, 11,
  249, 236, 124, 99, 99, 228, 73, 58, 196, 242, 43, 92, 44, 25, 59, 226, 28,
    176, 35, 161, 24, 235, 158, 131,
  154, 245, 191, 16, 120, 94, 123, 253, 33, 230, 69, 91, 131, 108, 197, 130,
    76, 231, 120, 85, 83, 209, 136,
  206, 78, 7, 235, 89, 146, 232, 22, 95, 14, 182, 222, 110, 71, 134, 72, 205,
    181, 212, 146, 2, 90, 119, 193,
  36, 15, 64, 70, 64, 244, 219, 207, 52, 229, 66, 213, 121, 239, 160, 45, 25,
    102, 211, 83, 123, 187, 205, 115,
  79, 9, 25, 146, 27, 214, 189, 136, 48, 39, 118, 231, 216, 123, 246, 194,
    117, 245, 246, 174, 74, 215, 196,
  237, 164, 120, 146, 250, 95, 19, 218, 53, 217, 207, 150, 158, 108, 97, 140,
    11, 158, 138, 141, 198, 15, 182,
  9, 197, 107, 120, 124, 141, 67, 199, 83, 8, 91, 236, 159, 106, 180, 118,
    132, 159, 159, 110, 29, 31, 30, 252,
  3, 91, 158, 51, 188, 210, 237, 73, 191, 184, 178, 134, 238, 108, 24, 100,
    70, 3, 44, 195, 167, 249, 247, 172,
  169, 73, 242, 222, 246, 179, 99, 189, 209, 62, 155, 173, 120, 95, 92, 101,
    22, 151, 55, 54, 47, 167, 204, 10,
  35, 55, 144, 172, 72, 57, 194, 231, 4, 103, 0, 227, 145, 237, 154, 79, 24,
    74, 46, 44, 224, 150, 121, 192,
  211, 216, 237, 185, 72, 163, 218, 192, 224, 144, 73, 207, 32, 227, 24, 227,
    146, 43, 150, 134, 215, 72, 151,
  195, 150, 183, 114, 89, 221, 71, 21, 180, 88, 243, 136, 199, 155, 35, 114,
    199, 29, 249, 36, 228, 214, 93,
  175, 141, 90, 214, 228, 218, 77, 107, 246, 187, 18, 25, 74, 72, 248, 96, 15,
    66, 27, 212, 30, 70, 123, 214,
  174, 172, 98, 221, 244, 184, 218, 123, 23, 46, 180, 219, 175, 9, 92, 253,
    186, 204, 73, 12, 76, 62, 92, 140,
  146, 61, 43, 114, 230, 125, 75, 87, 240, 219, 195, 125, 26, 200, 178, 47,
    252, 180, 24, 60, 251, 117, 21,
  173, 169, 248, 146, 195, 81, 208, 173, 13, 178, 173, 205, 227, 108, 100, 29,
    225, 144, 128, 72, 35, 190, 115,
  199, 214, 185, 221, 109, 117, 29, 42, 100, 181, 146, 57, 87, 35, 205, 154,
    96, 191, 38, 127, 186, 15, 160,
  172, 249, 224, 156, 185, 54, 176, 142, 123, 66, 183, 188, 240, 205, 210,
    222, 217, 91, 137, 97, 46, 18, 104,
  143, 97, 156, 126, 149, 234, 23, 133, 165, 178, 137, 34, 142, 47, 58, 126,
    168, 78, 2, 140, 117, 175, 48,
  127, 18, 199, 109, 101, 53, 169, 86, 118, 144, 146, 100, 199, 25, 246, 167,
    105, 250, 182, 165, 34, 165, 211,
  92, 59, 162, 17, 198, 121, 219, 220, 84, 170, 240, 140, 86, 163, 177, 213,
    199, 227, 216, 116, 146, 44, 175,
  163, 111, 220, 49, 141, 182, 118, 30, 191, 74, 227, 124, 89, 174, 88, 106,
    17, 151, 178, 221, 190, 71, 57,
  200, 237, 89, 190, 35, 154, 59, 205, 78, 91, 136, 85, 132, 110, 163, 175,
    115, 222, 176, 227, 134, 73, 85,
  136, 228, 37, 99, 82, 189, 219, 143, 65, 38, 211, 39, 211, 220, 71, 184,
    150, 235, 218, 138, 130, 222, 214,
  102, 5, 130, 49, 6, 138, 193, 197, 14, 235, 177, 169, 227, 121, 102, 190,
    214, 18, 225, 230, 142, 96, 16, 70,
  25, 8, 227, 29, 143, 243, 250, 26, 212, 240, 55, 138, 116, 223, 10, 155,
    185, 238, 236, 238, 230, 121, 194,
  166, 248, 130, 48, 17, 140, 146, 184, 98, 57, 36, 231, 191, 110, 149, 14,
    171, 166, 11, 193, 18, 64, 202,
  111, 22, 220, 52, 144, 231, 153, 19, 36, 101, 120, 234, 49, 200, 170, 95,
    99, 138, 242, 215, 77, 178, 179,
  144, 180, 238, 190, 83, 163, 41, 202, 62, 224, 197, 248, 234, 56, 35, 215,
    243, 173, 105, 74, 116, 218, 143,
  84, 45, 206, 235, 194, 218, 137, 189, 213, 117, 191, 21, 205, 19, 177, 158,
    233, 108, 109, 28, 144, 76, 11,
  180, 225, 74, 159, 189, 242, 4, 7, 29, 193, 61, 243, 92, 14, 186, 240, 220,
    220, 25, 45, 55, 121, 68, 178,
  174, 229, 0, 229, 112, 91, 129, 192, 228, 54, 42, 216, 183, 213, 180, 161,
    29, 171, 72, 237, 12, 68, 220,
  199, 28, 39, 33, 164, 35, 110, 236, 30, 115, 142, 58, 119, 62, 188, 219,
    191, 240, 213, 237, 135, 132, 162,
  213, 111, 204, 17, 75, 45, 208, 95, 33, 91, 47, 243, 169, 57, 61, 129, 239,
    142, 223, 165, 93, 73, 74, 81,
  229, 75, 109, 201, 123, 24, 206, 10, 216, 192, 16, 17, 230, 32, 137, 138,
    242, 91, 28, 144, 127, 65, 138,
  236, 252, 63, 226, 95, 15, 232, 222, 83, 68, 102, 19, 202, 155, 28, 68, 89,
    124, 195, 149, 192, 118, 228,
  250, 244, 7, 4, 143, 74, 229, 252, 61, 111, 121, 113, 127, 15, 217, 45, 254,
    208, 209, 49, 157, 99, 102, 216,
  187, 130, 241, 243, 30, 188, 227, 143, 106, 143, 80, 142, 89, 181, 25, 245,
    11, 184, 82, 217, 190, 208, 119,
  197, 18, 96, 36, 132, 123, 240, 50, 193, 191, 16, 105, 225, 234, 123, 56,
    237, 114, 150, 168, 246, 221, 7,
  197, 122, 102, 161, 29, 208, 211, 226, 212, 149, 237, 35, 102, 146, 29, 166,
    120, 219, 35, 35, 231, 228, 142,
  65, 198, 112, 56, 35, 154, 185, 32, 180, 214, 252, 47, 251, 171, 43, 128,
    167, 42, 99, 184, 98, 74, 145, 158,
  114, 78, 79, 36, 242, 50, 57, 247, 175, 52, 240, 126, 185, 107, 97, 166,
    221, 202, 179, 75, 111, 44, 217, 97,
  16, 148, 167, 156, 64, 34, 60, 176, 249, 176, 73, 232, 164, 117, 62, 166,
    186, 157, 103, 199, 112, 233, 254,
  13, 183, 212, 116, 51, 13, 214, 201, 150, 9, 173, 174, 64, 253, 214, 224,
    73, 200, 82, 8, 57, 7, 145, 215,
  173, 116, 243, 251, 234, 87, 178, 182, 193, 210, 199, 47, 167, 233, 215,
    118, 190, 34, 211, 151, 6, 57, 12,
  226, 1, 34, 72, 14, 192, 217, 249, 122, 119, 0, 129, 244, 173, 125, 107,
    194, 58, 159, 246, 236, 151, 183,
  49, 181, 202, 188, 165, 97, 242, 193, 42, 169, 129, 150, 97, 253, 236, 100,
    122, 15, 122, 194, 240, 191, 196,
  43, 171, 77, 75, 81, 158, 234, 214, 222, 88, 238, 34, 203, 218, 168, 216,
    160, 12, 100, 130, 115, 215, 112,
  200, 57, 224, 118, 197, 122, 76, 119, 183, 49, 54, 157, 55, 157, 48, 109,
    74, 209, 90, 219, 67, 147, 107, 21,
  114, 161, 137, 18, 99, 33, 84, 114, 196, 142, 56, 199, 77, 166, 41, 74, 9,
    187, 107, 168, 146, 60, 194, 52,
  213, 87, 79, 188, 240, 236, 177, 220, 71, 28, 141, 33, 180, 202, 18, 26, 32,
    216, 7, 35, 240, 224, 243, 200,
  61, 235, 22, 59, 40, 141, 186, 218, 90, 254, 247, 81, 149, 196, 73, 147,
    144, 88, 159, 228, 58, 154, 236,
  117, 203, 22, 240, 210, 25, 117, 89, 204, 204, 210, 44, 81, 70, 141, 152,
    164, 83, 181, 164, 98, 58, 182, 48,
  70, 214, 227, 32, 28, 114, 43, 7, 85, 130, 233, 245, 123, 141, 119, 78, 104,
    172, 221, 198, 86, 24, 216, 102,
  20, 35, 24, 61, 183, 16, 50, 64, 233, 156, 86, 117, 99, 202, 155, 191, 222,
    86, 137, 26, 31, 111, 30, 25,
  189, 180, 182, 176, 67, 121, 45, 172, 161, 99, 82, 185, 50, 5, 3, 39, 31,
    94, 7, 255, 0, 90, 186, 175, 16,
  52, 62, 39, 240, 205, 214, 167, 107, 28, 139, 120, 208, 236, 22, 248, 249,
    162, 99, 216, 251, 245, 175, 49,
  179, 22, 177, 111, 187, 212, 111, 101, 91, 168, 155, 239, 130, 119, 103, 0,
    255, 0, 62, 49, 94, 167, 165, 92,
  197, 171, 105, 241, 193, 109, 58, 219, 77, 52, 126, 103, 155, 180, 23, 118,
    30, 221, 7, 227, 154, 156, 35,
  122, 168, 252, 255, 0, 224, 9, 37, 99, 199, 229, 157, 221, 26, 214, 233, 60,
    169, 32, 24, 193, 24, 57, 174,
  203, 193, 58, 68, 58, 190, 149, 44, 95, 104, 217, 118, 141, 247, 15, 70, 7,
    166, 43, 150, 215, 152, 220, 222,
  166, 165, 230, 121, 198, 77, 201, 185, 163, 96, 132, 41, 198, 119, 31, 190,
    114, 79, 3, 184, 32, 226, 186,
  45, 15, 198, 54, 182, 31, 101, 73, 39, 158, 61, 139, 185, 213, 45, 145, 195,
    145, 199, 108, 17, 158, 121,
  169, 167, 10, 124, 237, 75, 98, 150, 168, 197, 241, 60, 18, 105, 183, 15,
    109, 42, 109, 101, 98, 63, 31, 240,
  53, 153, 165, 166, 232, 164, 199, 113, 94, 161, 226, 196, 210, 60, 79, 225,
    166, 191, 141, 72, 150, 52, 220,
  178, 119, 79, 99, 94, 91, 166, 221, 69, 5, 218, 219, 179, 110, 82, 112, 107,
    26, 212, 249, 22, 154, 137, 171,
  59, 50, 229, 182, 173, 21, 188, 94, 66, 197, 185, 148, 243, 129, 154, 43,
    126, 107, 141, 39, 73, 133, 18, 56,
  22, 71, 126, 91, 3, 52, 86, 28, 201, 235, 97, 242, 174, 228, 62, 36, 209,
    82, 218, 107, 61, 103, 78, 191,
  146, 113, 61, 192, 143, 105, 27, 100, 134, 82, 56, 29, 122, 18, 50, 61, 248,
    239, 204, 186, 68, 26, 180, 126,
  54, 75, 177, 163, 73, 107, 120, 145, 249, 194, 6, 67, 182, 110, 66, 183,
    205, 140, 13, 193, 143, 61, 5, 102,
  90, 233, 151, 186, 129, 134, 29, 62, 238, 105, 230, 143, 99, 183, 152, 118,
    4, 151, 128, 48, 57, 206, 14,
  224, 9, 250, 246, 175, 96, 240, 235, 95, 88, 248, 127, 200, 241, 26, 195,
    53, 213, 170, 51, 9, 1, 206, 245,
  11, 157, 196, 244, 220, 57, 7, 215, 25, 245, 175, 70, 52, 163, 57, 54, 180,
    51, 15, 16, 182, 141, 167, 37,
  157, 221, 253, 146, 168, 121, 140, 170, 81, 84, 188, 120, 76, 49, 220, 50,
    6, 55, 40, 235, 236, 43, 153, 241,
  86, 129, 111, 31, 135, 173, 161, 125, 66, 102, 130, 75, 129, 34, 149, 140,
    100, 240, 112, 113, 244, 207, 25,
  239, 93, 202, 207, 96, 250, 73, 99, 23, 219, 100, 141, 183, 170, 200, 67,
    148, 45, 193, 96, 79, 67, 180, 156,
  1, 219, 129, 94, 115, 227, 207, 18, 79, 119, 163, 233, 175, 111, 120, 193,
    166, 145, 226, 158, 21, 32, 111,
  112, 191, 43, 127, 120, 103, 158, 132, 114, 115, 91, 73, 56, 243, 57, 234,
    138, 118, 183, 153, 197, 70, 39,
  211, 238, 62, 203, 12, 225, 216, 70, 198, 7, 251, 191, 48, 36, 227, 219,
    156, 214, 157, 159, 131, 245, 31,
  17, 232, 114, 106, 118, 58, 132, 119, 18, 59, 102, 226, 209, 254, 66, 31,
    57, 228, 147, 140, 158, 196, 224,
  123, 245, 174, 69, 46, 202, 180, 143, 188, 171, 171, 41, 141, 64, 200, 32,
    12, 99, 219, 2, 189, 111, 192, 62,
  32, 208, 172, 173, 77, 172, 80, 253, 146, 228, 70, 171, 52, 141, 110, 88,
    203, 130, 64, 203, 0, 114, 50, 14,
  1, 199, 124, 10, 195, 15, 8, 202, 77, 61, 136, 71, 37, 225, 223, 8, 93, 222,
    202, 47, 245, 41, 36, 181, 150,
  50, 68, 118, 230, 61, 178, 22, 143, 229, 228, 31, 186, 6, 49, 211, 218, 181,
    180, 207, 0, 175, 140, 46, 53,
  13, 88, 203, 246, 43, 47, 182, 201, 12, 48, 65, 24, 118, 108, 96, 7, 206,
    113, 140, 254, 160, 246, 174, 243,
  91, 211, 181, 61, 107, 195, 119, 201, 165, 203, 109, 5, 247, 152, 223, 103,
    156, 41, 70, 104, 183, 130, 200,
  79, 85, 36, 228, 31, 240, 230, 184, 127, 134, 143, 168, 91, 65, 117, 111,
    229, 203, 36, 214, 151, 134, 7,
  128, 158, 96, 80, 7, 7, 208, 19, 188, 123, 144, 113, 93, 17, 132, 21, 149,
    139, 219, 67, 148, 215, 180, 201,
  180, 141, 89, 224, 242, 158, 25, 2, 249, 69, 221, 72, 46, 155, 74, 110, 3,
    176, 33, 73, 30, 245, 52, 176,
  106, 195, 72, 69, 133, 164, 150, 36, 17, 134, 249, 242, 241, 162, 103, 106,
    169, 60, 128, 55, 30, 7, 25, 61,
  43, 119, 80, 240, 197, 225, 215, 111, 110, 53, 155, 139, 134, 158, 226, 225,
    154, 17, 198, 90, 48, 197, 81,
  155, 176, 1, 71, 0, 15, 231, 76, 255, 0, 132, 90, 250, 234, 75, 101, 180,
    25, 211, 36, 70, 105, 111, 99, 193,
  220, 202, 197, 74, 12, 30, 185, 199, 7, 220, 243, 140, 30, 73, 81, 169, 204,
    185, 22, 140, 70, 77, 206, 163,
  110, 242, 89, 49, 186, 154, 226, 8, 96, 121, 98, 134, 86, 36, 196, 252, 130,
    167, 113, 195, 16, 118, 133, 35,
  177, 39, 142, 210, 180, 211, 38, 142, 111, 12, 104, 56, 243, 81, 23, 37, 71,
    3, 105, 99, 223, 248, 127, 51,
  248, 67, 103, 161, 105, 200, 53, 56, 175, 117, 80, 169, 12, 239, 3, 52, 112,
    151, 145, 130, 177, 206, 213, 7,
  190, 59, 149, 24, 7, 173, 116, 241, 234, 218, 214, 177, 160, 93, 65, 225,
    184, 70, 157, 160, 89, 131, 28,
  151, 19, 162, 189, 196, 187, 206, 2, 133, 25, 228, 228, 1, 142, 58, 124,
    227, 179, 168, 156, 221, 152, 229,
  123, 88, 243, 233, 109, 69, 253, 209, 158, 226, 233, 119, 200, 76, 146, 30,
    128, 18, 114, 127, 157, 105, 218,
  223, 75, 167, 221, 249, 176, 94, 202, 147, 60, 45, 18, 18, 48, 160, 48, 198,
    114, 122, 122, 230, 189, 81,
  124, 33, 97, 115, 101, 103, 114, 116, 91, 104, 166, 133, 162, 157, 10, 140,
    1, 181, 149, 154, 55, 198, 3, 2,
  3, 46, 72, 224, 224, 244, 206, 121, 31, 138, 26, 69, 165, 133, 246, 144,
    182, 204, 187, 238, 146, 99, 42,
  174, 55, 1, 185, 0, 63, 137, 222, 7, 208, 214, 147, 161, 42, 81, 111, 154,
    214, 19, 41, 193, 169, 91, 120,
  131, 69, 93, 21, 226, 69, 150, 214, 53, 138, 4, 0, 22, 44, 48, 184, 92, 113,
    201, 239, 239, 154, 196, 213,
  124, 27, 170, 233, 147, 42, 57, 0, 224, 47, 3, 130, 125, 1, 174, 175, 193,
    122, 21, 253, 154, 181, 237, 132,
  255, 0, 103, 134, 86, 242, 202, 148, 243, 119, 99, 251, 233, 211, 215, 146,
    65, 244, 174, 215, 198, 141, 4,
  48, 233, 54, 210, 71, 228, 207, 117, 57, 88, 103, 41, 242, 175, 0, 16, 79,
    161, 221, 198, 114, 65, 7, 222,
  165, 83, 83, 135, 52, 157, 138, 79, 91, 163, 201, 17, 53, 141, 19, 77, 146,
    63, 58, 57, 33, 152, 21, 120,
  203, 103, 102, 49, 215, 183, 113, 210, 178, 222, 209, 78, 156, 215, 130, 45,
    146, 19, 149, 97, 210, 189, 15,
  197, 158, 30, 139, 79, 183, 196, 177, 79, 36, 42, 159, 49, 71, 218, 20, 231,
    158, 188, 254, 62, 213, 194, 93,
  207, 15, 246, 66, 195, 107, 35, 180, 17, 184, 80, 91, 7, 39, 190, 8, 234,
    58, 224, 214, 120, 154, 50, 133,
  154, 122, 26, 69, 243, 38, 84, 212, 53, 123, 139, 38, 140, 198, 168, 67,
    174, 114, 104, 167, 53, 164, 51,
  201, 178, 85, 103, 80, 50, 152, 244, 205, 21, 132, 101, 4, 181, 70, 107, 83,
    172, 131, 81, 130, 202, 217,
  205, 180, 129, 174, 137, 89, 221, 97, 108, 144, 112, 48, 3, 116, 227, 252,
    120, 174, 255, 0, 195, 222, 50,
  131, 196, 154, 181, 205, 136, 142, 213, 17, 45, 190, 84, 40, 190, 100, 132,
    182, 214, 45, 216, 169, 4, 125,
  208, 58, 154, 240, 31, 237, 59, 155, 93, 68, 220, 194, 234, 6, 112, 98, 231,
    107, 14, 227, 223, 156, 213,
  253, 22, 227, 254, 42, 31, 182, 91, 239, 137, 80, 180, 170, 187, 190, 238,
    122, 143, 113, 201, 227, 243, 174,
  172, 58, 116, 229, 109, 211, 37, 104, 125, 7, 29, 197, 149, 133, 163, 217,
    233, 162, 209, 82, 220, 180, 32,
  68, 191, 44, 82, 115, 141, 203, 215, 230, 227, 62, 173, 158, 121, 175, 156,
    175, 101, 188, 212, 53, 27, 139,
  171, 197, 17, 78, 242, 179, 200, 49, 181, 81, 137, 201, 0, 30, 156, 146,
    113, 94, 159, 161, 93, 105, 54, 119,
  122, 172, 247, 87, 141, 103, 63, 148, 205, 9, 159, 2, 20, 221, 212, 100,
    114, 73, 32, 17, 156, 240, 49, 143,
  94, 19, 197, 214, 241, 71, 171, 71, 117, 0, 243, 97, 149, 51, 149, 4, 198,
    7, 4, 97, 136, 30, 167, 233, 138,
  210, 163, 114, 142, 186, 14, 94, 70, 60, 101, 32, 146, 84, 12, 146, 6, 80,
    173, 145, 200, 195, 6, 56, 56,
  227, 238, 224, 253, 77, 118, 90, 14, 181, 161, 217, 233, 165, 110, 124, 247,
    189, 105, 139, 148, 142, 51,
  156, 96, 109, 5, 177, 211, 169, 224, 31, 189, 210, 184, 6, 57, 12, 73, 206,
    121, 235, 159, 206, 187, 13, 11,
  194, 122, 214, 177, 178, 254, 206, 207, 237, 43, 34, 48, 138, 221, 38, 85,
    146, 92, 171, 32, 61, 126, 85, 4,
  28, 147, 140, 113, 89, 211, 151, 179, 149, 214, 224, 149, 206, 203, 78, 241,
    80, 187, 209, 230, 211, 5, 235,
  9, 231, 121, 2, 155, 112, 82, 72, 145, 241, 134, 25, 198, 8, 36, 252, 222,
    160, 87, 97, 165, 88, 217, 233,
  22, 122, 157, 205, 147, 186, 234, 215, 208, 151, 50, 200, 219, 188, 217, 66,
    146, 132, 244, 85, 57, 39, 184,
  228, 215, 207, 247, 214, 151, 86, 243, 93, 217, 223, 195, 228, 222, 43, 149,
    154, 55, 194, 180, 108, 27, 158,
  63, 19, 211, 219, 181, 123, 62, 157, 241, 4, 234, 154, 37, 150, 157, 166,
    232, 187, 181, 20, 181, 196, 81,
  59, 5, 137, 85, 20, 46, 71, 168, 201, 10, 1, 192, 247, 21, 172, 106, 243,
    174, 89, 111, 248, 130, 54, 94, 77,
  72, 232, 12, 154, 220, 118, 173, 168, 194, 113, 17, 249, 124, 192, 156, 97,
    78, 50, 1, 231, 160, 39, 234,
  107, 51, 72, 241, 95, 135, 180, 75, 187, 125, 56, 139, 91, 111, 62, 81, 230,
    69, 8, 249, 119, 118, 102, 199,
  202, 167, 32, 14, 112, 79, 78, 153, 34, 144, 241, 45, 159, 139, 244, 187,
    141, 17, 180, 249, 70, 181, 5, 155,
  44, 177, 204, 48, 174, 202, 2, 19, 150, 193, 4, 18, 51, 144, 48, 71, 25, 3,
    52, 253, 43, 194, 240, 89, 120,
  38, 239, 74, 191, 95, 33, 174, 34, 243, 46, 221, 98, 243, 74, 187, 100, 160,
    11, 234, 20, 47, 92, 12, 134,
  228, 114, 107, 90, 73, 217, 37, 174, 129, 123, 187, 156, 70, 171, 167, 201,
    225, 159, 16, 46, 138, 126, 117,
  105, 1, 251, 102, 67, 102, 54, 108, 179, 128, 114, 60, 207, 92, 255, 0, 116,
    117, 4, 26, 236, 117, 29, 71,
  65, 209, 124, 5, 28, 159, 36, 81, 234, 99, 230, 85, 109, 239, 54, 199, 193,
    194, 159, 66, 163, 208, 103, 173,
  115, 154, 142, 128, 205, 167, 220, 120, 138, 91, 196, 111, 42, 24, 161, 145,
    196, 70, 52, 222, 177, 162, 2,
  50, 57, 44, 66, 156, 12, 1, 154, 199, 241, 103, 131, 239, 116, 121, 224, 22,
    81, 221, 94, 219, 76, 30, 56,
  201, 143, 123, 196, 87, 44, 202, 66, 231, 182, 230, 4, 127, 181, 232, 77,
    102, 224, 233, 202, 252, 187, 108,
  59, 189, 142, 143, 194, 126, 40, 131, 87, 213, 134, 153, 31, 218, 45, 44,
    222, 41, 150, 77, 242, 180, 140,
  232, 192, 40, 78, 202, 15, 204, 199, 59, 114, 54, 14, 72, 206, 116, 60, 65,
    165, 233, 250, 126, 159, 163,
  218, 88, 196, 173, 115, 102, 140, 240, 201, 41, 204, 141, 146, 49, 185, 177,
    200, 63, 54, 7, 64, 114, 6, 49,
  94, 121, 164, 249, 186, 82, 89, 223, 137, 163, 5, 164, 204, 72, 27, 185, 32,
    18, 199, 176, 198, 79, 225, 239,
  91, 82, 235, 96, 234, 150, 183, 55, 119, 38, 117, 183, 182, 84, 111, 148,
    128, 88, 62, 224, 20, 117, 239,
  140, 158, 79, 62, 184, 165, 237, 97, 40, 55, 61, 91, 208, 77, 244, 69, 253,
    70, 234, 109, 46, 51, 119, 117,
  41, 142, 119, 192, 142, 24, 126, 67, 33, 236, 50, 123, 119, 39, 176, 230,
    182, 190, 30, 248, 138, 206, 215,
  77, 213, 35, 213, 245, 36, 151, 201, 153, 111, 204, 143, 16, 32, 48, 7, 126,
    220, 130, 204, 126, 85, 227,
  253, 161, 180, 118, 174, 63, 81, 213, 46, 110, 17, 175, 110, 7, 155, 60,
    209, 249, 113, 70, 138, 73, 183,
  140, 30, 152, 199, 183, 60, 242, 113, 207, 28, 227, 216, 40, 188, 185, 91,
    73, 174, 210, 198, 221, 142, 100,
  146, 108, 144, 49, 211, 229, 94, 73, 244, 30, 245, 199, 70, 94, 206, 90,
    106, 38, 236, 118, 250, 219, 89,
  124, 72, 240, 234, 221, 43, 53, 182, 171, 167, 96, 186, 238, 202, 152, 219,
    0, 156, 18, 51, 180, 237, 231,
  142, 9, 39, 38, 184, 115, 3, 218, 233, 191, 96, 42, 30, 101, 124, 179, 39,
    32, 117, 252, 191, 26, 185, 52,
  186, 125, 145, 242, 172, 245, 59, 187, 140, 134, 142, 89, 35, 143, 201, 67,
    25, 4, 21, 0, 242, 73, 28, 115,
  192, 206, 121, 233, 89, 239, 117, 189, 219, 96, 242, 211, 146, 1, 57, 199,
    166, 104, 173, 82, 82, 41, 74,
  209, 58, 127, 10, 65, 104, 241, 76, 247, 114, 168, 116, 194, 0, 199, 182, 1,
    162, 185, 164, 75, 139, 145,
  242, 57, 8, 63, 184, 51, 69, 113, 184, 93, 238, 105, 26, 182, 86, 177, 87,
    196, 122, 85, 174, 141, 175, 77,
  101, 103, 169, 197, 169, 66, 131, 112, 154, 51, 156, 31, 238, 158, 217, 30,
    222, 181, 147, 20, 243, 68, 172,
  81, 202, 135, 82, 172, 125, 65, 174, 151, 88, 210, 116, 223, 182, 221, 27,
    43, 132, 72, 82, 234, 81, 149, 63,
  43, 33, 249, 148, 15, 66, 62, 101, 199, 160, 28, 103, 57, 199, 185, 75, 51,
    111, 110, 144, 66, 198, 117, 230,
  89, 11, 182, 24, 144, 56, 32, 143, 151, 161, 233, 158, 190, 213, 235, 184,
    187, 182, 102, 108, 234, 126, 33,
  139, 81, 142, 201, 173, 162, 138, 59, 150, 141, 69, 200, 242, 243, 25, 117,
    206, 78, 211, 198, 8, 218, 113,
  245, 172, 157, 74, 250, 255, 0, 81, 187, 65, 168, 74, 51, 31, 221, 10, 161,
    85, 65, 244, 0, 123, 82, 196,
  170, 178, 98, 40, 212, 47, 222, 27, 215, 56, 192, 60, 103, 146, 58, 158,
    254, 135, 181, 91, 72, 18, 254, 197,
  167, 146, 104, 214, 72, 89, 73, 94, 174, 202, 115, 208, 119, 251, 188, 253,
    65, 233, 147, 89, 201, 182, 238,
  201, 69, 59, 150, 181, 48, 199, 12, 48, 1, 34, 243, 44, 155, 179, 147, 200,
    192, 253, 63, 47, 203, 222, 126,
  19, 143, 183, 232, 145, 182, 161, 108, 202, 214, 44, 26, 206, 85, 10, 155,
    35, 35, 24, 192, 251, 195, 57, 63,
  48, 234, 73, 175, 0, 16, 205, 47, 239, 82, 221, 196, 68, 228, 16, 191, 40,
    230, 189, 71, 225, 111, 139, 111,
  116, 237, 72, 105, 119, 169, 191, 79, 154, 23, 219, 51, 14, 99, 193, 200,
    27, 186, 21, 237, 131, 200, 207,
  167, 21, 49, 138, 110, 204, 164, 237, 177, 232, 122, 231, 131, 116, 111, 26,
    235, 17, 46, 167, 4, 208, 234,
  118, 207, 177, 230, 182, 81, 139, 136, 192, 200, 15, 237, 200, 228, 255, 0,
    90, 242, 143, 16, 199, 107, 225,
  47, 136, 174, 108, 204, 183, 98, 205, 145, 226, 41, 47, 45, 40, 76, 21, 109,
    167, 161, 33, 67, 1, 129, 180,
  145, 138, 247, 141, 58, 202, 210, 225, 239, 53, 45, 178, 45, 196, 177, 162,
    77, 28, 141, 242, 20, 218, 10,
  177, 94, 217, 2, 190, 121, 241, 196, 145, 232, 62, 57, 212, 180, 251, 72,
    13, 181, 138, 58, 183, 151, 16, 85,
  96, 25, 21, 138, 171, 16, 112, 55, 19, 131, 131, 129, 85, 37, 37, 173, 181,
    7, 228, 79, 225, 221, 81, 44,
  252, 65, 30, 167, 171, 222, 92, 253, 178, 230, 103, 146, 254, 227, 202, 102,
    104, 147, 25, 85, 202, 244, 50,
  55, 7, 142, 20, 40, 238, 64, 245, 125, 34, 226, 209, 32, 185, 181, 182, 157,
    167, 203, 139, 171, 104, 46, 56,
  146, 24, 95, 177, 83, 234, 200, 195, 156, 144, 49, 206, 120, 175, 14, 180,
    177, 186, 75, 52, 212, 108, 111,
  96, 153, 24, 160, 147, 46, 65, 138, 66, 114, 3, 131, 142, 252, 2, 122, 245,
    173, 127, 12, 233, 254, 48, 187,
  241, 131, 91, 219, 92, 8, 47, 238, 97, 59, 218, 241, 140, 106, 241, 174, 27,
    28, 13, 195, 24, 4, 109, 30,
  189, 65, 57, 218, 141, 88, 171, 39, 184, 186, 88, 245, 203, 161, 165, 248,
    223, 195, 239, 166, 218, 205, 34,
  71, 42, 57, 87, 104, 217, 90, 38, 7, 25, 195, 12, 110, 206, 114, 61, 171,
    93, 47, 180, 253, 13, 116, 251, 75,
  139, 184, 213, 167, 79, 41, 29, 200, 203, 72, 129, 80, 147, 233, 146, 249,
    252, 125, 171, 203, 161, 248, 131,
  113, 225, 69, 109, 42, 239, 76, 113, 171, 193, 116, 86, 238, 29, 196, 2, 75,
    49, 44, 172, 122, 146, 10, 16,
  64, 193, 25, 61, 14, 107, 191, 77, 102, 198, 239, 194, 246, 62, 33, 213, 17,
    30, 222, 40, 133, 203, 25, 206,
  242, 168, 207, 199, 25, 35, 118, 54, 16, 7, 86, 0, 14, 107, 105, 202, 250,
    193, 234, 63, 83, 207, 252, 117,
  240, 243, 90, 135, 95, 212, 53, 29, 61, 109, 101, 182, 158, 99, 36, 104,
    178, 5, 124, 176, 12, 199, 159, 246,
  139, 119, 28, 15, 194, 184, 115, 99, 46, 158, 72, 185, 70, 75, 142, 163,
    205, 233, 147, 158, 71, 111, 196,
  31, 94, 107, 213, 124, 109, 227, 6, 22, 22, 178, 104, 122, 173, 164, 145,
    92, 63, 204, 99, 8, 237, 180, 174,
  122, 30, 87, 167, 113, 158, 69, 121, 63, 246, 169, 213, 117, 66, 247, 119,
    88, 1, 91, 18, 58, 130, 72, 3,
  160, 24, 192, 201, 236, 7, 243, 174, 44, 68, 96, 180, 87, 185, 5, 72, 110,
    164, 138, 66, 199, 84, 146, 52,
  231, 32, 47, 152, 125, 178, 14, 23, 159, 173, 89, 109, 102, 103, 12, 175,
    26, 201, 17, 24, 203, 174, 199, 60,
  127, 178, 112, 62, 130, 171, 75, 60, 215, 49, 199, 16, 68, 142, 56, 137, 42,
    145, 231, 106, 19, 140, 245, 39,
  159, 215, 154, 45, 196, 38, 124, 18, 174, 16, 116, 57, 32, 156, 251, 87, 59,
    104, 106, 55, 52, 109, 52, 200,
  110, 140, 119, 17, 74, 100, 183, 10, 90, 88, 114, 67, 195, 130, 112, 27,
    140, 28, 158, 132, 100, 156, 244,
  205, 91, 189, 176, 182, 109, 38, 61, 66, 40, 210, 33, 47, 202, 35, 86, 206,
    71, 60, 183, 190, 71, 78, 223,
  201, 182, 186, 164, 81, 91, 188, 17, 15, 244, 136, 71, 238, 201, 56, 201,
    94, 14, 125, 202, 227, 4, 250, 30,
  156, 231, 62, 89, 46, 69, 178, 172, 241, 201, 20, 103, 247, 139, 25, 24,
    202, 177, 234, 63, 26, 202, 87, 52,
  148, 85, 154, 68, 250, 76, 186, 124, 75, 40, 191, 152, 198, 185, 27, 48,
    122, 209, 89, 19, 32, 114, 185, 201,
  28, 209, 79, 146, 47, 86, 204, 213, 205, 13, 71, 254, 63, 117, 143, 251, 8,
    191, 254, 133, 45, 99, 71, 254,
  177, 191, 222, 63, 206, 138, 43, 210, 95, 3, 249, 141, 151, 109, 191, 227,
    206, 127, 161, 254, 85, 173, 224,
  95, 249, 24, 99, 255, 0, 174, 79, 255, 0, 162, 94, 138, 40, 150, 209, 4, 99,
    201, 255, 0, 33, 59, 159, 250,
  238, 191, 251, 53, 122, 23, 129, 63, 228, 55, 101, 245, 63, 206, 138, 42,
    104, 124, 79, 208, 158, 167, 177,
  201, 255, 0, 37, 4, 255, 0, 216, 18, 79, 253, 13, 43, 230, 239, 136, 255, 0,
    242, 63, 106, 191, 239, 197,
  255, 0, 162, 82, 138, 42, 167, 177, 76, 207, 240, 175, 252, 132, 175, 63,
    235, 205, 255, 0, 154, 215, 190,
  120, 23, 254, 67, 182, 255, 0, 246, 5, 131, 255, 0, 70, 207, 69, 20, 47,
    133, 250, 161, 163, 133, 248, 215,
  255, 0, 37, 6, 211, 254, 193, 73, 255, 0, 161, 201, 87, 237, 191, 228, 141,
    233, 31, 245, 213, 63, 244, 99,
  209, 69, 17, 218, 126, 159, 228, 15, 99, 206, 110, 63, 213, 222, 125, 31,
    249, 138, 199, 176, 255, 0, 93, 39,
  251, 148, 81, 92, 107, 102, 76, 118, 47, 31, 249, 5, 159, 247, 90, 164, 135,
    172, 159, 238, 183, 254, 131,
  69, 21, 155, 216, 210, 4, 208, 255, 0, 200, 50, 79, 160, 254, 149, 163, 172,
    127, 200, 179, 164, 127, 215, 7,
  255, 0, 208, 168, 162, 176, 251, 95, 49, 63, 137, 152, 7, 238, 175, 227, 69,
    20, 86, 194, 63, 255, 217
};
/*
+--------------------------------------------------------------------------+
| CHStone : a suite of benchmark programs for C-based High-Level Synthesis |
| ======================================================================== |
|                                                                          |
| * Collected and Modified : Y. Hara, H. Tomiyama, S. Honda,               |
|                            H. Takada and K. Ishii                        |
|                            Nagoya University, Japan                      |
|                                                                          |
| * Remark :                                                               |
|    1. This source code is modified to unify the formats of the benchmark |
|       programs in CHStone.                                               |
|    2. Test vectors are added for CHStone.                                |
|    3. If "main_result" is 0 at the end of the program, the program is    |
|       correctly executed.                                                |
|    4. Please follow the copyright of each benchmark program.             |
+--------------------------------------------------------------------------+
*/
/*
 * Copyright (C) 2008
 * Y. Hara, H. Tomiyama, S. Honda, H. Takada and K. Ishii
 * Nagoya University, Japan
 * All rights reserved.
 *
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis. The authors disclaims any and all warranties, 
 * whether express, implied, or statuary, including any implied warranties or 
 * merchantability or of fitness for a particular purpose. In no event shall the
 * copyright-holder be liable for any incidental, punitive, or consequential damages
 * of any kind whatsoever arising from the use of these programs. This disclaimer
 * of warranty extends to the user of these programs and user's customers, employees,
 * agents, transferees, successors, and assigns.
 *
 */
/*
 *  Transformation: JPEG -> BMP
 *  
 *  @(#) $Id: jpeg2bmp.c,v 1.2 2003/07/18 10:19:21 honda Exp $ 
 */

/*
 * Buffer for reading JPEG file
 */
unsigned char JpegFileBuf[JPEG_FILE_SIZE];



void jpeg_read (unsigned char *read_buf);

void
jpeg2bmp_main ()
{
  int i, ci;
  unsigned char *c;

  /*
   *  Store in buffer
   */
  c = JpegFileBuf;
  for (i = 0; i < JPEGSIZE; i++)
    {
      ci = hana[i];
      *c++ = ci;
    }

  jpeg_read (JpegFileBuf);

}





int
main ()
{
      main_result = 0;
      jpeg2bmp_main ();

      return main_result;
    }
