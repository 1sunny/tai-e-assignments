#!/bin/bash

cp src/main/java/pascal/taie/analysis/pta/ci/Solver.java Solver.java

zip -u A5.zip Solver.java

rm Solver.java
