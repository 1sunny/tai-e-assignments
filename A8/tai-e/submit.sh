#!/bin/bash

cp src/main/java/pascal/taie/analysis/pta/plugin/taint/TaintAnalysiss.java TaintAnalysiss.java

cp src/main/java/pascal/taie/analysis/pta/cs/Solver.java Solver.java

zip -u A8.zip TaintAnalysiss.java Solver.java

rm TaintAnalysiss.java Solver.java
