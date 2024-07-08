# Copyright TU Wien
# Licensed under the Solderpad Hardware License v2.1, see LICENSE.txt for details
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.1


    .text
    .global main
main:
    la              a0, vdata_start
    addi a1, a0, 32

    li              t0, 8
    vsetvli         t0, t0, e32,m2,tu,mu
    
        
    vle32.v          v2, (a0)
    vle32.v          v4, (a1)
    
    vdiv.vv          v0, v2, v4
    
    vse32.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .int           2        #V2 start
    .int           40
    .int           -100
    .int           300
    .int           -1000
    .int           4000
    .int           1
    .int           8001     #V2 end
    .int           2        #V4 start
    .int           10
    .int           25
    .int           -3
    .int           -50
    .int           5
    .int           2
    .int           1000     #V4 end
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start: 
    .int           1        #v0 start
    .int           4
    .int           -4
    .int           -100
    .int           20
    .int           800
    .int           0
    .int           8        #V0 end
    .int           2
    .int           10
    .int           25
    .int           -3
    .int           -50
    .int           5
    .int           2
    .int           1000
vref_end:
