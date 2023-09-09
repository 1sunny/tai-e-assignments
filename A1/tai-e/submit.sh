#!/bin/bash

cp ./src/main/java/pascal/taie/analysis/dataflow/analysis/LiveVariableAnalysis.java LiveVariableAnalysis.java 
cp ./src/main/java/pascal/taie/analysis/dataflow/solver/IterativeSolver.java IterativeSolver.java
cp ./src/main/java/pascal/taie/analysis/dataflow/solver/Solver.java Solver.java

zip -u A1.zip LiveVariableAnalysis.java IterativeSolver.java Solver.java

rm LiveVariableAnalysis.java IterativeSolver.java Solver.java
