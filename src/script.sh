#!/bin/bash

fst_dice_loc=0

pushd dice &> /dev/null

for file in `ls *.fst`; do
    fst_dice_loc=$(( $fst_dice_loc + `cat $file | wc -l` ))
done
for file in `ls *.fsti`; do
    fst_dice_loc=$(( $fst_dice_loc + `cat $file | wc -l` ))
done

popd &> /dev/null

echo "F* DICE LOC: $fst_dice_loc"

pushd obj &> /dev/null

c_dice_loc_c=$(( `cat DICE_Core.c | wc -l` + `cat HWState.c | wc -l` ))
c_dice_loc_h=$(( `cat DICE_Core.h | wc -l` + `cat HWState.h | wc -l` + `cat HWAbstraction.h | wc -l` ))

echo "C DICE LOC: $c_dice_loc_c"
echo "H DICE LOC: $c_dice_loc_h"

popd &> /dev/null

fst_l0_asn1_loc=0
fst_l0_x509_loc=0
fst_l0_riot_loc=0

pushd riot/asn1 &> /dev/null

for file in `ls *.fst`; do
    fst_l0_asn1_loc=$(( $fst_l0_asn1_loc + `cat $file | wc -l` ))
done
for file in `ls *.fsti`; do
    fst_l0_asn1_loc=$(( $fst_l0_asn1_loc + `cat $file | wc -l` ))
done

popd &> /dev/null

pushd riot/x509 &> /dev/null

for file in `ls *.fst`; do
    fst_l0_x509_loc=$(( $fst_l0_x509_loc + `cat $file | wc -l` ))
done
for file in `ls *.fsti`; do
    fst_l0_x509_loc=$(( $fst_l0_x509_loc + `cat $file | wc -l` ))
done

popd &> /dev/null

pushd riot &> /dev/null

for file in `ls *.fst`; do
    fst_l0_riot_loc=$(( $fst_l0_riot_loc + `cat $file | wc -l` ))
done
for file in `ls *.fsti`; do
    fst_l0_riot_loc=$(( $fst_l0_riot_loc + `cat $file | wc -l` ))
done

popd &> /dev/null

echo "F* ASN1 LOC: $fst_l0_asn1_loc"
echo "F* X509 LOC: $fst_l0_x509_loc"
echo "F* RIoT LOC: $fst_l0_riot_loc"
echo "F* L0 LOC: $(( $fst_l0_riot_loc + $fst_l0_x509_loc + $fst_l0_asn1_loc ))"


c_l0_hacl_file_name="Hacl_Lib.c"
c_l0_hacl_loc=0

c_l0_test_file1="RIoT_Test.c"
c_l0_test_file2="RIoT_Test_Definitions.c"
c_l0_test_loc=0

c_l0_asn1_x509_file="ASN1_X509.c"
c_l0_asn1_x509_loc=0

c_l0_sum=0

pushd obj &> /dev/null

for file in `ls *.c`; do
    if [ "$file" == "DICE_Core.c" ]
    then
	continue
    fi

    if [ "$file" == "DICE_Test.c" ]
    then
	continue
    fi

    if [ "$file" == "HWState.c" ]
    then
	continue
    fi
    
    if [ "$file" == $c_l0_hacl_file_name ]
    then
	c_l0_hacl_loc=`cat $file | wc -l `
    fi

    if [ "$file" == $c_l0_asn1_x509_file ]
    then
	c_l0_asn1_x509_loc=`cat $file | wc -l `
    fi

    if [ "$file" == $c_l0_test_file1 ]
    then
	c_l0_test_loc=$(( $c_l0_test_loc + `cat $file | wc -l` ))
    fi

    if [ "$file" == $c_l0_test_file2 ]
    then
	c_l0_test_loc=$(( $c_l0_test_loc + `cat $file | wc -l` ))
    fi

    c_l0_sum=$(( $c_l0_sum  +  `cat $file | wc -l`))

    #echo "$file = `cat $file | wc -l`"
done

echo "C L0 LOC TOTAL: $c_l0_sum"
echo "C L0 LOC HACL*: $c_l0_hacl_loc"
echo "C L0 LOC Tests: $c_l0_test_loc"
echo "C L0 LOC ASN1/X509: $c_l0_asn1_x509_loc"

c_l0_loc_l0_ours=$(($c_l0_sum - $c_l0_hacl_loc - $c_l0_test_loc))

echo "C L0 LOC ours: $c_l0_loc_l0_ours"

h_sum=0
for file in `ls *.h`; do
    if [ "$file" == "DICE_Core.h" ]
    then
	continue
    fi

    if [ "$file" == "DICE_Test.h" ]
    then
	continue
    fi

    if [ "$file" == "HWState.h" ]
    then
	continue
    fi

    if [ "$file" == "HWAbstraction.h" ]
    then
	continue
    fi

    h_sum=$(( $h_sum  +  `cat $file | wc -l`))
    #echo "$file = `cat $file | wc -l`"
done

echo "H L0 LOC: $h_sum"

popd &> /dev/null
