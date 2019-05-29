#!/bin/bash


let tests=0
for i in `ls | grep test` ; do
    if ! test -d $i ; then
      continue ;
    fi
    God=$(tail -1 $i/output/oracle.txt);
    Puny=$(tail -1 $i/program_optimized_output);
    NumGod=$(echo $God | awk '{print $NF}')
    NumPuny=$(echo $Puny | awk '{print $NF}')
    if [ $NumGod -lt $NumPuny ]
    then
      let tests=$tests+1 ;
      echo $i
      echo "God's"
      echo $NumGod
      echo "Ours"
      echo $NumPuny
    fi
done

echo "Different Tests:"
echo "$tests"
