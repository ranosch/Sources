LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -6*x^2*y^4*z-11*x^2*y^3*z^2+6*x*y^4*z^2-6*x^2*y^2*z^3+11*x*y^3*z^3-x^2*y*z^4+6*x*y^2*z^4+x*y*z^5;
bfct(F);
tst_status(1);$
