LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -12*x^4*y^2*z-10*x^3*y^3*z+6*x^2*y^4*z+4*x*y^5*z-12*x^4*y*z^2-5*x^3*y^2*z^2-3*x^2*y^3*z^2+5*x^3*y*z^3-3*x^2*y^2*z^3-5*x*y^3*z^3+6*x^2*y*z^4+x*y*z^5;
bfct(F);
tst_status(1);$
