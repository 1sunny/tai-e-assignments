#!/bin/bash

cp ./src/main/java/pascal/taie/analysis/dataflow/analysis/DeadCodeDetection.java DeadCodeDetection.java

zip -u A3.zip DeadCodeDetection.java

rm DeadCodeDetection.java
