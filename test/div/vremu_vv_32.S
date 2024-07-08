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
    
    vremu.vv          v0, v2, v4
    
    vse32.v          v0, (a0)
   
  

    la              a0, vdata_start
    la              a1, vdata_end
    j               spill_cache


    .data
    .align 10
    .global vdata_start
    .global vdata_end
vdata_start:
    .int           2    #v2 start
    .int           45
    .int           -113
    .int           301
    .int           -50  
    .int           4004
    .int           2
    .int           8000 #v2 end
    .int           3    #v4 start
    .int           10
    .int           25
    .int           -3
    .int           -1012
    .int           5
    .int           2
    .int           1000 #v4 end
vdata_end:

    .align 10
    .global vref_start
    .global vref_end
vref_start:
    .int           2    #result start
    .int           5
    .int           8
    .int           301
    .int           962
    .int           4
    .int           0
    .int           0    #result end
    .int           3
    .int           10
    .int           25
    .int           -3
    .int           -1012
    .int           5
    .int           2
    .int           1000
vref_end:
