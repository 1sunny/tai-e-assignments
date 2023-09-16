#!/bin/bash

cp src/main/java/pascal/taie/analysis/graph/callgraph/CHABuilder.java CHABuilder.java

cp src/main/java/pascal/taie/analysis/dataflow/inter/InterConstantPropagation.java InterConstantPropagation.java

cp src/main/java/pascal/taie/analysis/dataflow/inter/InterSolver.java InterSolver.java

zip -u A4.zip CHABuilder.java InterConstantPropagation.java InterSolver.java

rm CHABuilder.java InterConstantPropagation.java InterSolver.java
