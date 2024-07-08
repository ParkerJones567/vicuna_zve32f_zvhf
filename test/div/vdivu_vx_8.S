# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 32
    li              t1, 4
    vsetvli         t0, t0, e8,m2,tu,mu
    
        
    vle8.v          v2, (a0)
    
    vdivu.vx          v0, v2, t1
    
    vse8.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word 0x03020100 # 3 | 2 | 1 | 0
    .word 0x07060504 # 7 | 6 | 5 | 4
    .word 0xfcfdfeff # -4 | -3 | -2 | -1
    .word 0xf8f9fafb # -8 | -7 | -6 | -5
    .word 0x03020100 # 3 | 2 | 1 | 0
    .word 0x07060504 # 7 | 6 | 5 | 4
    .word 0xfcfdfeff # -4 | -3 | -2 | -1
    .word 0xf8f9fafb # -8 | -7 | -6 | -5
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word 0x00000000 # 0 | 0 | 0 | 0
    .word 0x01010101 # 1 | 1 | 1 | 1
    .word 0x3f3f3f3f # 63 | 63 | 63 | 63
    .word 0x3e3e3e3e # 62 | 62 | 62 | 62
    .word 0x00000000 # 0 | 0 | 0 | 0
    .word 0x01010101 # 1 | 1 | 1 | 1
    .word 0x3f3f3f3f # 63 | 63 | 63 | 63
    .word 0x3e3e3e3e # 62 | 62 | 62 | 62
vref_end:
