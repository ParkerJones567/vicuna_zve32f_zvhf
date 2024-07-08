# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 16
    li              t1, 4
    vsetvli         t0, t0, e16,m2,tu,mu
    
        
    vle16.v          v2, (a0)
    
    vrem.vx          v0, v2, t1
    
    vse16.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word 0x00010000 # 1 | 0
    .word 0x00030002 # 3 | 2
    .word 0x00050004 # 5 | 4
    .word 0x00070006 # 7 | 6
    .word 0xfffeffff # -2 | -1
    .word 0xfffcfffd # -4 | -3
    .word 0xfffafffb # -6 | -5
    .word 0xfff8fff9 # -8 | -7
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word 0x00010000 # 1 | 0
    .word 0x00030002 # 3 | 2
    .word 0x00010000 # 1 | 0
    .word 0x00030002 # 3 | 2
    .word 0xfffeffff # -2 | -1
    .word 0x0000fffd # 0 | -3
    .word 0xfffeffff # -2 | -1
    .word 0x0000fffd # 0 | -3
vref_end:
