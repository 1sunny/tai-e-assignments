class Cast {

    public static void main(String[] args) {
        A a1 = new B();
        a1.f = 111;
        B b1 = (B)a1;
        int x = b1.f;
    }

}

class A {
    int f;
}

class B extends A {

}