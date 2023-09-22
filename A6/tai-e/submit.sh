#!/bin/bash

cp src/main/java/pascal/taie/analysis/pta/cs/Solver.java Solver.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_1CallSelector.java _1CallSelector.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_1ObjSelector.java _1ObjSelector.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_1TypeSelector.java _1TypeSelector.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_2CallSelector.java _2CallSelector.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_2ObjSelector.java _2ObjSelector.java

cp src/main/java/pascal/taie/analysis/pta/core/cs/selector/_2TypeSelector.java _2TypeSelector.java

zip -u A6.zip Solver.java _1CallSelector.java _1ObjSelector.java _1TypeSelector.java _2CallSelector.java _2ObjSelector.java _2TypeSelector.java

rm Solver.java _1CallSelector.java _1ObjSelector.java _1TypeSelector.java _2CallSelector.java _2ObjSelector.java _2TypeSelector.java
