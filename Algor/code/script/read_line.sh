#!/bin/bash

while read line; do
  if [ `echo $line | grep tile | wc -l ` -eq 1 ] ; then
    echo "hello"
    continue
  fi

done < $file
