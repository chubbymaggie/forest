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

#define Num 2048

/*
+--------------------------------------------------------------------------+
| * Test Vectors (added for CHStone)                                       |
|     inRdbfr, inPMV, inPMV : input data                                   |
|     outPMV, outmvfs : expected output data                               |
+--------------------------------------------------------------------------+
*/
const unsigned char inRdbfr[Num] = {
  0, 104, 120, 48, 72, 32, 160, 192, 192, 64, 56, 248, 248, 88, 136, 224, 200,
  208, 176, 72, 96, 40, 184, 160, 32, 32, 120, 168, 64, 32, 72, 184,
  216, 240, 0, 216, 192, 64, 112, 48, 160, 152, 40, 176, 32, 32, 248, 200,
  104, 24, 216, 240, 128, 176, 72, 232, 240, 184, 48, 120, 48, 192, 64, 168,
  160, 128, 160, 160, 232, 208, 104, 120, 232, 120, 8, 184, 120, 200, 64, 160,
  200, 224, 64, 168, 40, 120, 80, 104, 16, 0, 8, 120, 144, 136, 80, 144,
  72, 24, 128, 216, 216, 24, 80, 16, 64, 32, 200, 112, 128, 144, 88, 24, 112,
  120, 32, 104, 72, 176, 24, 16, 184, 56, 24, 200, 152, 152, 48, 48,
  136, 80, 240, 8, 216, 200, 240, 32, 168, 112, 48, 56, 40, 192, 232, 32, 48,
  232, 232, 32, 0, 88, 208, 24, 240, 72, 120, 96, 248, 136, 224, 208,
  8, 184, 192, 144, 88, 48, 144, 136, 112, 192, 96, 240, 200, 160, 184, 160,
  24, 48, 208, 152, 128, 184, 184, 144, 144, 168, 240, 144, 160, 168, 48,
  48,
  24, 200, 144, 120, 208, 56, 96, 72, 48, 88, 80, 200, 248, 208, 248, 40, 136,
  112, 32, 8, 8, 80, 192, 40, 32, 224, 56, 192, 200, 56, 56, 232,
  200, 80, 120, 8, 184, 216, 232, 80, 168, 128, 32, 216, 136, 104, 248, 168,
  248, 8, 192, 168, 192, 56, 240, 192, 208, 136, 120, 48, 224, 112, 168, 80,
  192, 96, 80, 120, 120, 16, 120, 48, 168, 168, 160, 224, 128, 24, 72, 24,
  248, 240, 152, 160, 208, 56, 192, 56, 88, 128, 192, 136, 128, 208, 112,
  40,
  64, 192, 32, 176, 80, 56, 168, 208, 24, 168, 168, 248, 240, 136, 96, 32, 56,
  184, 8, 136, 16, 0, 176, 40, 0, 32, 104, 160, 56, 88, 232, 56,
  0, 240, 184, 232, 88, 32, 176, 0, 216, 248, 184, 40, 16, 80, 8, 208, 64,
  224, 72, 40, 72, 72, 144, 80, 144, 120, 136, 64, 184, 160, 136, 16,
  48, 104, 232, 104, 104, 72, 208, 72, 192, 184, 40, 56, 232, 72, 160, 80,
  152, 232, 248, 32, 224, 40, 0, 168, 24, 96, 112, 160, 152, 8, 32, 160,
  104, 208, 32, 24, 248, 8, 248, 144, 120, 16, 192, 88, 152, 176, 200, 160,
  152, 160, 96, 168, 240, 16, 248, 176, 24, 216, 0, 56, 80, 248, 96, 8,
  128, 32, 192, 104, 48, 208, 240, 184, 128, 80, 56, 192, 0, 112, 176, 48, 96,
  56, 24, 56, 24, 32, 24, 96, 80, 0, 64, 112, 48, 24, 88, 56,
  152, 224, 160, 192, 184, 72, 248, 128, 8, 8, 104, 104, 200, 48, 136, 136,
  208, 144, 80, 40, 136, 96, 8, 208, 160, 104, 160, 80, 64, 96, 176, 144,
  8, 56, 88, 88, 208, 120, 48, 240, 240, 96, 248, 192, 104, 128, 248, 24, 104,
  72, 64, 120, 248, 192, 48, 192, 32, 80, 144, 16, 80, 96, 112, 184,
  56, 80, 248, 232, 0, 40, 248, 56, 192, 32, 192, 96, 248, 48, 136, 224, 80,
  0, 192, 128, 104, 120, 208, 128, 0, 176, 216, 8, 192, 96, 16, 40,
  184, 96, 32, 72, 80, 192, 104, 104, 136, 0, 16, 160, 24, 104, 48, 8, 24,
  152, 120, 128, 72, 32, 176, 112, 104, 120, 16, 32, 144, 160, 56, 240,
  0, 232, 184, 24, 16, 208, 200, 240, 200, 200, 104, 112, 24, 208, 128, 168,
  248, 64, 152, 120, 64, 224, 128, 208, 120, 216, 16, 152, 48, 144, 240, 80,
  144, 224, 48, 160, 192, 248, 0, 128, 120, 128, 160, 232, 168, 208, 112, 112,
  104, 184, 8, 192, 56, 176, 40, 96, 64, 72, 104, 216, 152, 216, 80, 152,
  184, 216, 32, 56, 32, 64, 240, 152, 240, 168, 136, 8, 232, 168, 128, 88, 72,
  128, 8, 192, 48, 120, 112, 32, 144, 208, 192, 216, 16, 176, 168, 160,
  168, 88, 136, 56, 8, 64, 0, 80, 216, 104, 64, 80, 88, 208, 64, 80, 200, 24,
  120, 160, 80, 72, 56, 216, 24, 56, 72, 40, 72, 0, 56, 136,
  56, 200, 72, 136, 88, 72, 136, 240, 0, 176, 176, 152, 192, 248, 224, 240,
  72, 8, 112, 232, 200, 120, 16, 0, 40, 48, 64, 72, 32, 136, 104, 152,
  16, 240, 184, 80, 0, 152, 32, 176, 128, 120, 0, 160, 40, 64, 112, 40, 80,
  48, 144, 96, 168, 0, 152, 72, 184, 136, 88, 152, 184, 48, 88, 152,
  96, 216, 240, 184, 200, 136, 64, 104, 112, 232, 0, 208, 176, 128, 112, 248,
  144, 248, 120, 112, 0, 120, 240, 88, 88, 88, 8, 248, 80, 8, 64, 216,
  240, 56, 56, 144, 112, 208, 144, 72, 16, 160, 136, 216, 176, 112, 56, 8,
  168, 104, 72, 40, 176, 88, 40, 120, 24, 40, 56, 104, 40, 160, 232, 160,
  24, 144, 144, 232, 120, 144, 112, 96, 136, 176, 8, 128, 112, 184, 96, 120,
  64, 112, 0, 184, 80, 72, 184, 80, 144, 72, 120, 200, 168, 32, 24, 0,
  144, 72, 24, 248, 24, 152, 72, 128, 0, 8, 224, 32, 72, 72, 48, 112, 232, 16,
  240, 24, 64, 32, 232, 120, 168, 200, 152, 112, 8, 144, 0, 120,
  112, 0, 112, 144, 72, 160, 24, 216, 112, 128, 224, 152, 104, 136, 40, 0, 16,
  144, 48, 248, 136, 48, 64, 88, 152, 208, 248, 16, 112, 224, 184, 168,
  40, 168, 64, 248, 144, 104, 200, 144, 152, 16, 168, 192, 240, 96, 72, 136,
  216, 136, 0, 32, 192, 112, 240, 160, 248, 184, 16, 48, 232, 88, 160, 16,
  104, 176, 144, 136, 24, 240, 184, 160, 8, 16, 32, 56, 176, 144, 168, 168,
  56, 88, 88, 104, 248, 184, 96, 32, 128, 88, 224, 240, 32, 120, 216, 136,
  8, 72, 80, 104, 120, 152, 32, 96, 232, 80, 232, 24, 80, 200, 208, 216, 184,
  16, 56, 40, 216, 208, 128, 120, 16, 16, 80, 200, 144, 104, 160, 72,
  24, 136, 176, 32, 192, 120, 136, 80, 16, 88, 208, 160, 16, 232, 40, 24, 144,
  208, 32, 16, 88, 192, 48, 176, 152, 24, 160, 32, 80, 24, 240, 80,
  160, 152, 160, 128, 80, 88, 40, 184, 208, 144, 48, 200, 200, 48, 112, 144,
  104, 224, 144, 224, 200, 8, 224, 240, 32, 152, 232, 16, 8, 80, 184, 40,
  184, 248, 64, 8, 232, 16, 88, 88, 8, 120, 128, 48, 240, 88, 64, 104, 104,
  248, 96, 240, 192, 152, 208, 56, 152, 240, 136, 8, 216, 24, 112, 168,
  88, 136, 80, 224, 136, 152, 40, 24, 248, 216, 152, 136, 96, 224, 64, 80, 56,
  56, 72, 8, 24, 64, 144, 24, 208, 216, 128, 120, 96, 168, 120, 152,
  112, 232, 136, 80, 72, 96, 152, 208, 72, 216, 64, 120, 120, 48, 232, 72,
  184, 176, 48, 232, 200, 184, 120, 72, 112, 128, 248, 160, 168, 216, 152,
  80,
  176, 112, 48, 152, 112, 64, 40, 200, 232, 80, 160, 56, 216, 192, 168, 72,
  40, 64, 208, 32, 224, 240, 24, 104, 232, 240, 168, 24, 248, 32, 80, 152,
  144, 160, 112, 120, 96, 240, 64, 160, 248, 248, 152, 48, 112, 88, 128, 232,
  240, 240, 232, 168, 120, 32, 152, 176, 104, 16, 80, 152, 240, 224, 128,
  16,
  48, 32, 216, 8, 104, 248, 184, 208, 216, 120, 80, 208, 128, 56, 112, 40,
  184, 16, 224, 168, 152, 248, 56, 144, 168, 224, 8, 168, 80, 136, 152, 48,
  96, 0, 184, 88, 192, 24, 16, 128, 0, 176, 152, 40, 96, 72, 192, 0, 32, 128,
  24, 240, 48, 248, 176, 120, 16, 168, 224, 72, 8, 200, 48, 176,
  112, 224, 160, 8, 152, 64, 16, 16, 240, 224, 64, 144, 128, 80, 184, 40, 232,
  200, 112, 248, 24, 112, 176, 128, 128, 56, 40, 152, 24, 184, 120, 104,
  72, 64, 200, 48, 224, 0, 56, 232, 32, 240, 184, 104, 104, 32, 192, 200, 200,
  64, 152, 72, 216, 216, 80, 0, 80, 0, 0, 160, 120, 40, 136, 240,
  32, 120, 152, 216, 56, 112, 16, 24, 8, 120, 104, 192, 144, 176, 8, 16, 96,
  104, 168, 80, 192, 232, 112, 112, 56, 88, 176, 240, 32, 176, 248, 80,
  176, 24, 224, 192, 8, 176, 168, 16, 232, 248, 16, 16, 104, 128, 232, 0, 32,
  240, 112, 32, 184, 184, 56, 232, 80, 144, 16, 72, 240, 208, 64, 176,
  240, 16, 136, 16, 80, 192, 24, 72, 216, 56, 80, 216, 32, 144, 72, 24, 64,
  248, 0, 224, 72, 32, 136, 232, 240, 72, 32, 88, 128, 104, 16, 8,
  32, 192, 224, 8, 152, 248, 224, 0, 176, 48, 16, 104, 216, 176, 24, 240, 200,
  80, 248, 208, 128, 200, 72, 8, 152, 128, 80, 120, 80, 152, 232, 200,
  168, 88, 16, 176, 232, 40, 72, 208, 232, 112, 240, 112, 80, 176, 176, 16,
  72, 120, 32, 184, 224, 80, 24, 176, 0, 208, 16, 56, 112, 16, 120, 160,
  24, 216, 128, 136, 192, 152, 248, 120, 160, 56, 192, 224, 0, 136, 112, 112,
  8, 8, 184, 168, 88, 160, 120, 160, 240, 168, 32, 40, 168, 88, 8, 16,
  24, 104, 104, 48, 248, 136, 72, 144, 128, 160, 216, 88, 240, 120, 232, 72,
  192, 200, 248, 192, 48, 240, 104, 208, 40, 104, 16, 128, 80, 224, 224, 56,
  56, 120, 40, 24, 176, 16, 184, 24, 176, 224, 168, 16, 184, 104, 136, 200,
  168, 208, 120, 200, 224, 40, 208, 16, 112, 160, 192, 224, 64, 40, 232,
  120,
  24, 232, 168, 80, 88, 144, 104, 72, 192, 112, 0, 112, 104, 224, 232, 160,
  112, 208, 176, 216, 56, 224, 224, 160, 104, 56, 176, 216, 192, 24, 208, 8,
  40, 56, 248, 8, 120, 184, 128, 40, 168, 56, 184, 192, 136, 96, 72, 216, 8,
  64, 72, 56, 16, 176, 144, 16, 128, 176, 136, 208, 120, 16, 184, 224,
  160, 216, 144, 88, 208, 200, 144, 96, 152, 200, 224, 208, 240, 120, 8, 104,
  184, 112, 168, 200, 112, 72, 0, 192, 0, 40, 120, 136, 112, 40, 152, 56,
  144, 32, 224, 240, 32, 192, 56, 200, 16, 136, 104, 192, 192, 0, 0, 0, 8,
  232, 104, 240, 88, 192, 8, 168, 216, 208, 184, 224, 240, 72, 152, 72,
  168, 184, 176, 216, 48, 144, 80, 32, 184, 208, 112, 160, 88, 88, 8, 144,
  144, 120, 152, 48, 200, 168, 112, 8, 160, 216, 240, 128, 104, 128, 144,
  248,
  64, 168, 136, 240, 160, 56, 136, 216, 80, 56, 192, 32, 64, 128, 80, 32, 32,
  96, 88, 200, 152, 72, 160, 16, 128, 200, 160, 144, 112, 16, 112, 152,
  56, 136, 56, 216, 8, 24, 192, 144, 176, 200, 48, 72, 40, 72, 240, 120, 120,
  160, 80, 152, 144, 216, 224, 152, 40, 144, 160, 88, 184, 184, 192, 128,
  0, 200, 72, 112, 208, 248, 152, 0, 152, 8, 40, 16, 168, 152, 64, 176, 88,
  24, 232, 136, 32, 152, 232, 208, 192, 240, 136, 0, 232, 200, 8, 216,
  104, 184, 64, 192, 8, 96, 184, 120, 208, 80, 16, 64, 136, 136, 72, 8, 112,
  184, 248, 120, 136, 8, 56, 232, 208, 96, 16, 64, 168, 112, 48, 32,
  184, 224, 72, 88, 128, 184, 72, 168, 224, 216, 160, 232, 64, 168, 48, 152,
  64, 152, 16, 200, 168, 56, 144, 192, 64, 120, 168, 8, 128, 216, 16, 8,
  104, 32, 128, 96, 160, 88, 136, 96, 56, 16, 128, 56, 88, 16, 208, 200, 24,
  96, 240, 32, 232, 192, 104, 168, 40, 0, 192, 40, 200, 96, 184, 8,
  72, 216, 104, 232, 112, 248, 8, 8, 248, 192, 152, 32, 0, 168, 232, 80, 248,
  64, 8, 24, 80, 32, 96, 240, 232, 48, 80, 16, 144, 200, 16, 48,
  88, 40, 112, 232, 88, 168, 56, 160, 232, 16, 128, 248, 48, 80, 200, 168,
  152, 72, 216, 224, 72, 208, 152, 192, 0, 224, 48, 136, 168, 96, 16, 152
};
const unsigned char out_ld_Rdptr[Num] = {
  72, 184, 216, 240, 0, 216, 192, 64, 112, 48, 160, 152, 40, 176, 32, 32, 248,
  200, 104, 24, 216, 240, 128, 176, 72, 232, 240, 184, 48, 120, 48, 192,
  64, 168, 160, 128, 160, 160, 232, 208, 104, 120, 232, 120, 8, 184, 120, 200,
  64, 160, 200, 224, 64, 168, 40, 120, 80, 104, 16, 0, 8, 120, 144, 136,
  80, 144, 72, 24, 128, 216, 216, 24, 80, 16, 64, 32, 200, 112, 128, 144, 88,
  24, 112, 120, 32, 104, 72, 176, 24, 16, 184, 56, 24, 200, 152, 152,
  48, 48, 136, 80, 240, 8, 216, 200, 240, 32, 168, 112, 48, 56, 40, 192, 232,
  32, 48, 232, 232, 32, 0, 88, 208, 24, 240, 72, 120, 96, 248, 136,
  224, 208, 8, 184, 192, 144, 88, 48, 144, 136, 112, 192, 96, 240, 200, 160,
  184, 160, 24, 48, 208, 152, 128, 184, 184, 144, 144, 168, 240, 144, 160,
  168,
  48, 48, 24, 200, 144, 120, 208, 56, 96, 72, 48, 88, 80, 200, 248, 208, 248,
  40, 136, 112, 32, 8, 8, 80, 192, 40, 32, 224, 56, 192, 200, 56,
  56, 232, 200, 80, 120, 8, 184, 216, 232, 80, 168, 128, 32, 216, 136, 104,
  248, 168, 248, 8, 192, 168, 192, 56, 240, 192, 208, 136, 120, 48, 224,
  112,
  168, 80, 192, 96, 80, 120, 120, 16, 120, 48, 168, 168, 160, 224, 128, 24,
  72, 24, 248, 240, 152, 160, 208, 56, 192, 56, 88, 128, 192, 136, 128, 208,
  112, 40, 64, 192, 32, 176, 80, 56, 168, 208, 24, 168, 168, 248, 240, 136,
  96, 32, 56, 184, 8, 136, 16, 0, 176, 40, 0, 32, 104, 160, 56, 88,
  232, 56, 0, 240, 184, 232, 88, 32, 176, 0, 216, 248, 184, 40, 16, 80, 8,
  208, 64, 224, 72, 40, 72, 72, 144, 80, 144, 120, 136, 64, 184, 160,
  136, 16, 48, 104, 232, 104, 104, 72, 208, 72, 192, 184, 40, 56, 232, 72,
  160, 80, 152, 232, 248, 32, 224, 40, 0, 168, 24, 96, 112, 160, 152, 8,
  32, 160, 104, 208, 32, 24, 248, 8, 248, 144, 120, 16, 192, 88, 152, 176,
  200, 160, 152, 160, 96, 168, 240, 16, 248, 176, 24, 216, 0, 56, 80, 248,
  96, 8, 128, 32, 192, 104, 48, 208, 240, 184, 128, 80, 56, 192, 0, 112, 176,
  48, 96, 56, 24, 56, 24, 32, 24, 96, 80, 0, 64, 112, 48, 24,
  88, 56, 152, 224, 160, 192, 184, 72, 248, 128, 8, 8, 104, 104, 200, 48, 136,
  136, 208, 144, 80, 40, 136, 96, 8, 208, 160, 104, 160, 80, 64, 96,
  176, 144, 8, 56, 88, 88, 208, 120, 48, 240, 240, 96, 248, 192, 104, 128,
  248, 24, 104, 72, 64, 120, 248, 192, 48, 192, 32, 80, 144, 16, 80, 96,
  112, 184, 56, 80, 248, 232, 0, 40, 248, 56, 192, 32, 192, 96, 248, 48, 136,
  224, 80, 0, 192, 128, 104, 120, 208, 128, 0, 176, 216, 8, 192, 96,
  16, 40, 184, 96, 32, 72, 80, 192, 104, 104, 136, 0, 16, 160, 24, 104, 48, 8,
  24, 152, 120, 128, 72, 32, 176, 112, 104, 120, 16, 32, 144, 160,
  56, 240, 0, 232, 184, 24, 16, 208, 200, 240, 200, 200, 104, 112, 24, 208,
  128, 168, 248, 64, 152, 120, 64, 224, 128, 208, 120, 216, 16, 152, 48,
  144,
  240, 80, 144, 224, 48, 160, 192, 248, 0, 128, 120, 128, 160, 232, 168, 208,
  112, 112, 104, 184, 8, 192, 56, 176, 40, 96, 64, 72, 104, 216, 152, 216,
  80, 152, 184, 216, 32, 56, 32, 64, 240, 152, 240, 168, 136, 8, 232, 168,
  128, 88, 72, 128, 8, 192, 48, 120, 112, 32, 144, 208, 192, 216, 16, 176,
  168, 160, 168, 88, 136, 56, 8, 64, 0, 80, 216, 104, 64, 80, 88, 208, 64, 80,
  200, 24, 120, 160, 80, 72, 56, 216, 24, 56, 72, 40, 72, 0,
  56, 136, 56, 200, 72, 136, 88, 72, 136, 240, 0, 176, 176, 152, 192, 248,
  224, 240, 72, 8, 112, 232, 200, 120, 16, 0, 40, 48, 64, 72, 32, 136,
  104, 152, 16, 240, 184, 80, 0, 152, 32, 176, 128, 120, 0, 160, 40, 64, 112,
  40, 80, 48, 144, 96, 168, 0, 152, 72, 184, 136, 88, 152, 184, 48,
  88, 152, 96, 216, 240, 184, 200, 136, 64, 104, 112, 232, 0, 208, 176, 128,
  112, 248, 144, 248, 120, 112, 0, 120, 240, 88, 88, 88, 8, 248, 80, 8,
  64, 216, 240, 56, 56, 144, 112, 208, 144, 72, 16, 160, 136, 216, 176, 112,
  56, 8, 168, 104, 72, 40, 176, 88, 40, 120, 24, 40, 56, 104, 40, 160,
  232, 160, 24, 144, 144, 232, 120, 144, 112, 96, 136, 176, 8, 128, 112, 184,
  96, 120, 64, 112, 0, 184, 80, 72, 184, 80, 144, 72, 120, 200, 168, 32,
  24, 0, 144, 72, 24, 248, 24, 152, 72, 128, 0, 8, 224, 32, 72, 72, 48, 112,
  232, 16, 240, 24, 64, 32, 232, 120, 168, 200, 152, 112, 8, 144,
  0, 120, 112, 0, 112, 144, 72, 160, 24, 216, 112, 128, 224, 152, 104, 136,
  40, 0, 16, 144, 48, 248, 136, 48, 64, 88, 152, 208, 248, 16, 112, 224,
  184, 168, 40, 168, 64, 248, 144, 104, 200, 144, 152, 16, 168, 192, 240, 96,
  72, 136, 216, 136, 0, 32, 192, 112, 240, 160, 248, 184, 16, 48, 232, 88,
  160, 16, 104, 176, 144, 136, 24, 240, 184, 160, 8, 16, 32, 56, 176, 144,
  168, 168, 56, 88, 88, 104, 248, 184, 96, 32, 128, 88, 224, 240, 32, 120,
  216, 136, 8, 72, 80, 104, 120, 152, 32, 96, 232, 80, 232, 24, 80, 200, 208,
  216, 184, 16, 56, 40, 216, 208, 128, 120, 16, 16, 80, 200, 144, 104,
  160, 72, 24, 136, 176, 32, 192, 120, 136, 80, 16, 88, 208, 160, 16, 232, 40,
  24, 144, 208, 32, 16, 88, 192, 48, 176, 152, 24, 160, 32, 80, 24,
  240, 80, 160, 152, 160, 128, 80, 88, 40, 184, 208, 144, 48, 200, 200, 48,
  112, 144, 104, 224, 144, 224, 200, 8, 224, 240, 32, 152, 232, 16, 8, 80,
  184, 40, 184, 248, 64, 8, 232, 16, 88, 88, 8, 120, 128, 48, 240, 88, 64,
  104, 104, 248, 96, 240, 192, 152, 208, 56, 152, 240, 136, 8, 216, 24,
  112, 168, 88, 136, 80, 224, 136, 152, 40, 24, 248, 216, 152, 136, 96, 224,
  64, 80, 56, 56, 72, 8, 24, 64, 144, 24, 208, 216, 128, 120, 96, 168,
  120, 152, 112, 232, 136, 80, 72, 96, 152, 208, 72, 216, 64, 120, 120, 48,
  232, 72, 184, 176, 48, 232, 200, 184, 120, 72, 112, 128, 248, 160, 168,
  216,
  152, 80, 176, 112, 48, 152, 112, 64, 40, 200, 232, 80, 160, 56, 216, 192,
  168, 72, 40, 64, 208, 32, 224, 240, 24, 104, 232, 240, 168, 24, 248, 32,
  80, 152, 144, 160, 112, 120, 96, 240, 64, 160, 248, 248, 152, 48, 112, 88,
  128, 232, 240, 240, 232, 168, 120, 32, 152, 176, 104, 16, 80, 152, 240,
  224,
  128, 16, 48, 32, 216, 8, 104, 248, 184, 208, 216, 120, 80, 208, 128, 56,
  112, 40, 184, 16, 224, 168, 152, 248, 56, 144, 168, 224, 8, 168, 80, 136,
  152, 48, 96, 0, 184, 88, 192, 24, 16, 128, 0, 176, 152, 40, 96, 72, 192, 0,
  32, 128, 24, 240, 48, 248, 176, 120, 16, 168, 224, 72, 8, 200,
  48, 176, 112, 224, 160, 8, 152, 64, 16, 16, 240, 224, 64, 144, 128, 80, 184,
  40, 232, 200, 112, 248, 24, 112, 176, 128, 128, 56, 40, 152, 24, 184,
  120, 104, 72, 64, 200, 48, 224, 0, 56, 232, 32, 240, 184, 104, 104, 32, 192,
  200, 200, 64, 152, 72, 216, 216, 80, 0, 80, 0, 0, 160, 120, 40,
  136, 240, 32, 120, 152, 216, 56, 112, 16, 24, 8, 120, 104, 192, 144, 176, 8,
  16, 96, 104, 168, 80, 192, 232, 112, 112, 56, 88, 176, 240, 32, 176,
  248, 80, 176, 24, 224, 192, 8, 176, 168, 16, 232, 248, 16, 16, 104, 128,
  232, 0, 32, 240, 112, 32, 184, 184, 56, 232, 80, 144, 16, 72, 240, 208,
  64, 176, 240, 16, 136, 16, 80, 192, 24, 72, 216, 56, 80, 216, 32, 144, 72,
  24, 64, 248, 0, 224, 72, 32, 136, 232, 240, 72, 32, 88, 128, 104,
  16, 8, 32, 192, 224, 8, 152, 248, 224, 0, 176, 48, 16, 104, 216, 176, 24,
  240, 200, 80, 248, 208, 128, 200, 72, 8, 152, 128, 80, 120, 80, 152,
  232, 200, 168, 88, 16, 176, 232, 40, 72, 208, 232, 112, 240, 112, 80, 176,
  176, 16, 72, 120, 32, 184, 224, 80, 24, 176, 0, 208, 16, 56, 112, 16,
  120, 160, 24, 216, 128, 136, 192, 152, 248, 120, 160, 56, 192, 224, 0, 136,
  112, 112, 8, 8, 184, 168, 88, 160, 120, 160, 240, 168, 32, 40, 168, 88,
  8, 16, 24, 104, 104, 48, 248, 136, 72, 144, 128, 160, 216, 88, 240, 120,
  232, 72, 192, 200, 248, 192, 48, 240, 104, 208, 40, 104, 16, 128, 80, 224,
  224, 56, 56, 120, 40, 24, 176, 16, 184, 24, 176, 224, 168, 16, 184, 104,
  136, 200, 168, 208, 120, 200, 224, 40, 208, 16, 112, 160, 192, 224, 64,
  40,
  232, 120, 24, 232, 168, 80, 88, 144, 104, 72, 192, 112, 0, 112, 104, 224,
  232, 160, 112, 208, 176, 216, 56, 224, 224, 160, 104, 56, 176, 216, 192,
  24,
  208, 8, 40, 56, 248, 8, 120, 184, 128, 40, 168, 56, 184, 192, 136, 96, 72,
  216, 8, 64, 72, 56, 16, 176, 144, 16, 128, 176, 136, 208, 120, 16,
  184, 224, 160, 216, 144, 88, 208, 200, 144, 96, 152, 200, 224, 208, 240,
  120, 8, 104, 184, 112, 168, 200, 112, 72, 0, 192, 0, 40, 120, 136, 112,
  40,
  152, 56, 144, 32, 224, 240, 32, 192, 56, 200, 16, 136, 104, 192, 192, 0, 0,
  0, 8, 232, 104, 240, 88, 192, 8, 168, 216, 208, 184, 224, 240, 72,
  152, 72, 168, 184, 176, 216, 48, 144, 80, 32, 184, 208, 112, 160, 88, 88, 8,
  144, 144, 120, 152, 48, 200, 168, 112, 8, 160, 216, 240, 128, 104, 128,
  144, 248, 64, 168, 136, 240, 160, 56, 136, 216, 80, 56, 192, 32, 64, 128,
  80, 32, 32, 96, 88, 200, 152, 72, 160, 16, 128, 200, 160, 144, 112, 16,
  112, 152, 56, 136, 56, 216, 8, 24, 192, 144, 176, 200, 48, 72, 40, 72, 240,
  120, 120, 160, 80, 152, 144, 216, 224, 152, 40, 144, 160, 88, 184, 184,
  192, 128, 0, 200, 72, 112, 208, 248, 152, 0, 152, 8, 40, 16, 168, 152, 64,
  176, 88, 24, 232, 136, 32, 152, 232, 208, 192, 240, 136, 0, 232, 200,
  8, 216, 104, 184, 64, 192, 8, 96, 184, 120, 208, 80, 16, 64, 136, 136, 72,
  8, 112, 184, 248, 120, 136, 8, 56, 232, 208, 96, 16, 64, 168, 112,
  48, 32, 184, 224, 72, 88, 128, 184, 72, 168, 224, 216, 160, 232, 64, 168,
  48, 152, 64, 152, 16, 200, 168, 56, 144, 192, 64, 120, 168, 8, 128, 216,
  16, 8, 104, 32, 128, 96, 160, 88, 136, 96, 56, 16, 128, 56, 88, 16, 208,
  200, 24, 96, 240, 32, 232, 192, 104, 168, 40, 0, 192, 40, 200, 96,
  184, 8, 72, 216, 104, 232, 112, 248, 8, 8, 248, 192, 152, 32, 0, 168, 232,
  80, 248, 64, 8, 24, 80, 32, 96, 240, 232, 48, 80, 16, 144, 200,
  16, 48, 88, 40, 112, 232, 88, 168, 56, 160, 232, 16, 128, 248, 48, 80, 200,
  168, 152, 72, 216, 224, 72, 208, 152, 192, 0, 224, 48, 136, 168, 96,
  16, 152, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 224, 227, 227, 227,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};
const int inPMV[2][2][2] = { {{45, 207}, {70, 41}}, {{4, 180}, {120, 216}} };
const int inmvfs[2][2] = { {232, 200}, {32, 240} };
const int outPMV[2][2][2] =
  { {{1566, 206}, {70, 41}}, {{1566, 206}, {120, 216}} };
const int outmvfs[2][2] = { {0, 200}, {0, 240} };

int evalue;


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
/* config.h, configuration defines                                          */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */

/* define NON_ANSI_COMPILER for compilers without function prototyping */
/* #define NON_ANSI_COMPILER */

#define _ANSI_ARGS_(x) x
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
/* global.h, global variables                                               */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */


/* mpeg2dec.h, MPEG specific defines                                        */
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
/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */

#define ERROR (-1)

#define SEQUENCE_END_CODE       0x1B7


/* mv_format */
#define MV_FIELD 0



/* choose between declaration (GLOBAL undefined)
 * and definition (GLOBAL defined)
 * GLOBAL is defined in exactly one file mpeg2dec.c)
 */


/* Get_Bits.c */
void Fill_Buffer _ANSI_ARGS_ ((void));
unsigned int Show_Bits _ANSI_ARGS_ ((int n));
unsigned int Get_Bits1 _ANSI_ARGS_ ((void));
void Flush_Buffer _ANSI_ARGS_ ((int n));
unsigned int Get_Bits _ANSI_ARGS_ ((int n));
int Get_Byte _ANSI_ARGS_ ((void));

/* getvlc.c */
int Get_motion_code _ANSI_ARGS_ ((void));
int Get_dmvector _ANSI_ARGS_ ((void));
int Get_coded_block_pattern _ANSI_ARGS_ ((void));


/* motion.c */
void motion_vector
_ANSI_ARGS_ ((int *PMV, int *dmvector, int h_r_size, int v_r_size, int dmv,
	      int mvscale, int full_pel_vector));

int System_Stream_Flag;

unsigned char ld_Rdbfr[2048];
unsigned char *ld_Rdptr, *ld_Rdmax;
unsigned int ld_Bfr;
int ld_Incnt;
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
/* getbits.c, bit level routines                                            */

/*
 * All modifications (mpeg2decode -> mpeg2play) are
 * Copyright (C) 1996, Stefan Eckart. All Rights Reserved.
 */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */


/* initialize buffer, call once before first getbits or showbits */
int
read (unsigned char *s1, const unsigned char *s2, int n)
{
  unsigned char *p1;
  const unsigned char *p2;
  int n_tmp;
  p1 = s1;
  p2 = s2;
  n_tmp = n;
  while (n_tmp-- > 0)
    {
      *p1 = *p2;
      p1++;
      p2++;
    }
  return n;
}
void
Fill_Buffer ()
{
  int Buffer_Level;
  unsigned char *p;
  p = ld_Rdbfr;


  Buffer_Level = read (ld_Rdbfr, inRdbfr, 2048);
  ld_Rdptr = ld_Rdbfr;

  if (System_Stream_Flag)
    ld_Rdmax -= 2048;


  /* end of the bitstream file */
  if (Buffer_Level < 2048)
    {
      /* just to be safe */
      if (Buffer_Level < 0)
	Buffer_Level = 0;

      /* pad until the next to the next 32-bit word boundary */
      while (Buffer_Level & 3)
	ld_Rdbfr[Buffer_Level++] = 0;

      /* pad the buffer with sequence end codes */
      while (Buffer_Level < 2048)
	{
	  ld_Rdbfr[Buffer_Level++] = SEQUENCE_END_CODE >> 24;
	  ld_Rdbfr[Buffer_Level++] = SEQUENCE_END_CODE >> 16;
	  ld_Rdbfr[Buffer_Level++] = SEQUENCE_END_CODE >> 8;
	  ld_Rdbfr[Buffer_Level++] = SEQUENCE_END_CODE & 0xff;
	}
    }
}

unsigned int
Show_Bits (N)
     int N;
{
  return ld_Bfr >> (unsigned)(32-N)%32;
}


/* return next bit (could be made faster than Get_Bits(1)) */

unsigned int
Get_Bits1 ()
{
  return Get_Bits (1);
}


/* advance by n bits */

void
Flush_Buffer (N)
     int N;
{
  int Incnt;

  ld_Bfr <<= N;

  Incnt = ld_Incnt -= N;

  if (Incnt <= 24)
    {
      if (ld_Rdptr < ld_Rdbfr + 2044)
	{
	  do
	    {
	      ld_Bfr |= *ld_Rdptr++ << (24 - Incnt);
	      Incnt += 8;
	    }
	  while (Incnt <= 24);
	}
      else
	{
	  do
	    {
	      if (ld_Rdptr >= ld_Rdbfr + 2048)
		Fill_Buffer ();
	      ld_Bfr |= *ld_Rdptr++ << (24 - Incnt);
	      Incnt += 8;
	    }
	  while (Incnt <= 24);
	}
      ld_Incnt = Incnt;
    }
}


/* return next n bits (right adjusted) */

unsigned int
Get_Bits (N)
     int N;
{
  unsigned int Val;

  Val = Show_Bits (N);
  Flush_Buffer (N);

  return Val;
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
/* getvlc.h, variable length code tables                                    */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */

/* NOTE: #define constants such as MACROBLOCK_QUANT are upper case 
   as per C programming convention. However, the MPEG document 
   (ISO/IEC 13818-2) lists them in all lower case (e.g. Annex B) */

/* NOTE: the VLC tables are in a flash format---a transformation
   of the tables in Annex B to a form more convenient towards 
   parallel (more than one-bit-at-a-time) decoding */


/* Table B-10, motion_code, codes 0001 ... 01xx */
const char MVtab0[8][2] = {
  {ERROR, 0}, {3, 3}, {2, 2}, {2, 2},
  {1, 1}, {1, 1}, {1, 1}, {1, 1}
};

/* Table B-10, motion_code, codes 0000011 ... 000011x */
const char MVtab1[8][2] = {
  {ERROR, 0}, {ERROR, 0}, {ERROR, 0}, {7, 6},
  {6, 6}, {5, 6}, {4, 5}, {4, 5}
};

/* Table B-10, motion_code, codes 0000001100 ... 000001011x */
const char MVtab2[12][2] = {
  {16, 9}, {15, 9}, {14, 9}, {13, 9}, {12, 9}, {11, 9},
  {10, 8}, {10, 8}, {9, 8}, {9, 8}, {8, 8}, {8, 8}
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
/* getvlc.c, variable length decoding                                       */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */

int
Get_motion_code ()
{
  int code;

  if (Get_Bits1 ())
    {
      return 0;
    }

  if ((code = Show_Bits (9)) >= 64)
    {
      code >>= 6;
      Flush_Buffer (MVtab0[code][1]);

      return Get_Bits1 ()? -MVtab0[code][0] : MVtab0[code][0];
    }

  if (code >= 24)
    {
      code >>= 3;
      Flush_Buffer (MVtab1[code][1]);

      return Get_Bits1 ()? -MVtab1[code][0] : MVtab1[code][0];
    }

  if ((code -= 12) < 0)
    return 0;

  Flush_Buffer (MVtab2[code][1]);
  return Get_Bits1 ()? -MVtab2[code][0] : MVtab2[code][0];
}

/* get differential motion vector (for dual prime prediction) */
int
Get_dmvector ()
{

  if (Get_Bits (1))
    {
      return Get_Bits (1) ? -1 : 1;
    }
  else
    {
      return 0;
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
/* motion.c, motion vector decoding                                         */

/* Copyright (C) 1996, MPEG Software Simulation Group. All Rights Reserved. */

/*
 * Disclaimer of Warranty
 *
 * These software programs are available to the user without any license fee or
 * royalty on an "as is" basis.  The MPEG Software Simulation Group disclaims
 * any and all warranties, whether express, implied, or statuary, including any
 * implied warranties or merchantability or of fitness for a particular
 * purpose.  In no event shall the copyright-holder be liable for any
 * incidental, punitive, or consequential damages of any kind whatsoever
 * arising from the use of these programs.
 *
 * This disclaimer of warranty extends to the user of these programs and user's
 * customers, employees, agents, transferees, successors, and assigns.
 *
 * The MPEG Software Simulation Group does not represent or warrant that the
 * programs furnished hereunder are free of infringement of any third-party
 * patents.
 *
 * Commercial implementations of MPEG-1 and MPEG-2 video, including shareware,
 * are subject to royalty fees to patent holders.  Many of these patents are
 * general enough such that they are unavoidable regardless of implementation
 * design.
 *
 */

/* private prototypes */
static void decode_motion_vector
_ANSI_ARGS_ ((int *pred, int r_size, int motion_code,
	      int motion_residualesidual, int full_pel_vector));

/* ISO/IEC 13818-2 sections 6.2.5.2, 6.3.17.2, and 7.6.3: Motion vectors */
void
motion_vectors (PMV, dmvector, motion_vertical_field_select, s,
		motion_vector_count, mv_format, h_r_size, v_r_size, dmv,
		mvscale)
     int PMV[2][2][2];
     int dmvector[2];
     int motion_vertical_field_select[2][2];
     int s, motion_vector_count, mv_format, h_r_size, v_r_size, dmv, mvscale;
{
  if (motion_vector_count == 1)
    {
      if (mv_format == MV_FIELD && !dmv)
	{
	  motion_vertical_field_select[1][s] =
	    motion_vertical_field_select[0][s] = Get_Bits (1);
	}

      motion_vector (PMV[0][s], dmvector, h_r_size, v_r_size, dmv, mvscale,
		     0);

      /* update other motion vector predictors */
      PMV[1][s][0] = PMV[0][s][0];
      PMV[1][s][1] = PMV[0][s][1];
    }
  else
    {
      motion_vertical_field_select[0][s] = Get_Bits (1);

      motion_vector (PMV[0][s], dmvector, h_r_size, v_r_size, dmv, mvscale,
		     0);

      motion_vertical_field_select[1][s] = Get_Bits (1);

      motion_vector (PMV[1][s], dmvector, h_r_size, v_r_size, dmv, mvscale,
		     0);
    }
}

/* get and decode motion vector and differential motion vector 
   for one prediction */
void
motion_vector (PMV, dmvector, h_r_size, v_r_size, dmv, mvscale,
	       full_pel_vector)
     int *PMV;
     int *dmvector;
     int h_r_size;
     int v_r_size;
     int dmv;			/* MPEG-2 only: get differential motion vectors */
     int mvscale;		/* MPEG-2 only: field vector in frame pic */
     int full_pel_vector;	/* MPEG-1 only */
{
  int motion_code;
  int motion_residual;

  /* horizontal component */
  /* ISO/IEC 13818-2 Table B-10 */
  motion_code = Get_motion_code ();

  motion_residual = (h_r_size != 0
		     && motion_code != 0) ? Get_Bits (h_r_size) : 0;

  decode_motion_vector (&PMV[0], h_r_size, motion_code, motion_residual,
			full_pel_vector);

  if (dmv)
    dmvector[0] = Get_dmvector ();


  /* vertical component */
  motion_code = Get_motion_code ();
  motion_residual = (v_r_size != 0
		     && motion_code != 0) ? Get_Bits (v_r_size) : 0;

  if (mvscale)
    PMV[1] >>= 1;		/* DIV 2 */

  decode_motion_vector (&PMV[1], v_r_size, motion_code, motion_residual,
			full_pel_vector);

  if (mvscale)
    PMV[1] <<= 1;

  if (dmv)
    dmvector[1] = Get_dmvector ();

}

/* calculate motion vector component */
/* ISO/IEC 13818-2 section 7.6.3.1: Decoding the motion vectors */
/* Note: the arithmetic here is more elegant than that which is shown 
   in 7.6.3.1.  The end results (PMV[][][]) should, however, be the same.  */

static void
decode_motion_vector (pred, r_size, motion_code, motion_residual,
		      full_pel_vector)
     int *pred;
     int r_size, motion_code, motion_residual;
     int full_pel_vector;	/* MPEG-1 (ISO/IEC 11172-1) support */
{
  int lim, vec;

  r_size = r_size % 32;
  lim = 16 << r_size;
  vec = full_pel_vector ? (*pred >> 1) : (*pred);

  if (motion_code > 0)
    {
      vec += ((motion_code - 1) << r_size) + motion_residual + 1;
      if (vec >= lim)
	vec -= lim + lim;
    }
  else if (motion_code < 0)
    {
      vec -= ((-motion_code - 1) << r_size) + motion_residual + 1;
      if (vec < -lim)
	vec += lim + lim;
    }
  *pred = full_pel_vector ? (vec << 1) : vec;
}




void
Initialize_Buffer ()
{
  ld_Incnt = 0;
  ld_Rdptr = ld_Rdbfr + 2048;
  ld_Rdmax = ld_Rdptr;
  ld_Bfr = 68157440;
  Flush_Buffer (0);		/* fills valid data into bfr */
}

int
main ()
{
  int i, j, k;
  int main_result;
  int PMV[2][2][2];
  int dmvector[2];
  int motion_vertical_field_select[2][2];
  int s, motion_vector_count, mv_format, h_r_size, v_r_size, dmv, mvscale;

      main_result = 0;
      evalue = 0;
      System_Stream_Flag = 0;
      s = 0;
      motion_vector_count = 1;
      mv_format = 0;
      h_r_size = 200;
      v_r_size = 200;
      dmv = 0;
      mvscale = 1;
      for (i = 0; i < 2; i++)
	{
	  dmvector[i] = 0;
	  for (j = 0; j < 2; j++)
	    {
	      motion_vertical_field_select[i][j] = inmvfs[i][j];
	      for (k = 0; k < 2; k++)
		PMV[i][j][k] = inPMV[i][j][k];
	    }
	}

      Initialize_Buffer ();
      motion_vectors (PMV, dmvector, motion_vertical_field_select, s,
		      motion_vector_count, mv_format, h_r_size, v_r_size, dmv,
		      mvscale);

      for (i = 0; i < 2; i++)
	for (j = 0; j < 2; j++)
	  {
	    main_result +=
	      (motion_vertical_field_select[i][j] != outmvfs[i][j]);
	    for (k = 0; k < 2; k++)
	      main_result += (PMV[i][j][k] != outPMV[i][j][k]);
	  }

  return main_result;

}
