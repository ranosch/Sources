LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = 36*x^4*y*z+66*x^3*y^2*z+36*x^2*y^3*z+6*x*y^4*z+49*x^3*y*z^2+48*x^2*y^2*z^2+11*x*y^3*z^2+14*x^2*y*z^3+6*x*y^2*z^3+x*y*z^4;
bfct(F);
tst_status(1);$
