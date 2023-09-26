#!/bin/bash

cp src/main/java/pascal/taie/analysis/dataflow/inter/InterConstantPropagation.java InterConstantPropagation.java

cp src/main/java/pascal/taie/analysis/dataflow/inter/InterSolver.java InterSolver.java

cp src/main/java/pascal/taie/analysis/dataflow/analysis/constprop/ConstantPropagation.java ConstantPropagation.java

zip -u A7.zip InterConstantPropagation.java InterSolver.java ConstantPropagation.java

rm InterConstantPropagation.java InterSolver.java ConstantPropagation.java
