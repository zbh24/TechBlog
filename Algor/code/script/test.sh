#!/bin/bash

for i in `cat input.txt`; do
    name=$(awk '{print $3}');
    echo $name;
done
