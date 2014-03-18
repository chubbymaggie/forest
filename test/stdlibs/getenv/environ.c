/*
 * =====================================================================================
 * /
 * |     Filename:  environ.c
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  03/17/2014 01:51:28 PM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */


char* __environ[1];
char* str = "PATH\x00hello\x00";
