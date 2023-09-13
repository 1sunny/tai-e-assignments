class Test {
    int unreachableSwitchBranch() {
        int x = 2, y;
        switch (x) {
            case 1: y = 100; break; // unreachable branch
            case 2: y = 200;
            case 3: y = 300; break; // fall through
            default: y = 666; // unreachable branch
        }
        return y;
    }
}