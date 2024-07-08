# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 32
    vsetvli         t0, t0, e8,m2,tu,mu
    
        
    vle8.v          v2, (a0)
    vle8.v          v4, (a1)
    
    vdivu.vv          v0, v2, v4
    
    vse8.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .word 0x7f9c2802 # 127 | -100 | 40 | 2  #V2 start
    .word 0x4c013780 # 76 | 1 | 55 | -128
    .word 0x7f9c2802 # 127 | -100 | 40 | 2
    .word 0x4c013780 # 76 | 1 | 55 | -128
    .word 0x7f9c2802 # 127 | -100 | 40 | 2
    .word 0x4c013780 # 76 | 1 | 55 | -128
    .word 0x7f9c2802 # 127 | -100 | 40 | 2
    .word 0x4c013780 # 76 | 1 | 55 | -128   #V2 end
    .word 0xfd190a02 # -3 | 25 | 10 | 2     #V4 start
    .word 0x7f0205ce # 127 | 2 | 5 | -50
    .word 0xfd190a02 # -3 | 25 | 10 | 2
    .word 0x7f0205ce # 127 | 2 | 5 | -50
    .word 0xfd190a02 # -3 | 25 | 10 | 2
    .word 0x7f0205ce # 127 | 2 | 5 | -50
    .word 0xfd190a02 # -3 | 25 | 10 | 2
    .word 0x7f0205ce # 127 | 2 | 5 | -50    #V4 end
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .word 0x00060401 # 0 | 6 | 4 | 1        #V0 start
    .word 0x00000b00 # 0 | 0 | 11 | 0
    .word 0x00060401 # 0 | 6 | 4 | 1
    .word 0x00000b00 # 0 | 0 | 11 | 0
    .word 0x00060401 # 0 | 6 | 4 | 1
    .word 0x00000b00 # 0 | 0 | 11 | 0
    .word 0x00060401 # 0 | 6 | 4 | 1
    .word 0x00000b00 # 0 | 0 | 11 | 0       #V0 end
    .word 0xfd190a02 
    .word 0x7f0205ce 
    .word 0xfd190a02 
    .word 0x7f0205ce 
    .word 0xfd190a02 
    .word 0x7f0205ce 
    .word 0xfd190a02 
    .word 0x7f0205ce 
vref_end:
