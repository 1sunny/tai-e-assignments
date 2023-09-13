#!/bin/bash

cp ./src/main/java/pascal/taie/analysis/dataflow/analysis/constprop/ConstantPropagation.java ConstantPropagation.java 
cp ./src/main/java/pascal/taie/analysis/dataflow/solver/WorkListSolver.java WorkListSolver.java
cp ./src/main/java/pascal/taie/analysis/dataflow/solver/Solver.java Solver.java

zip -u A2.zip ConstantPropagation.java WorkListSolver.java Solver.java

rm ConstantPropagation.java WorkListSolver.java Solver.java
