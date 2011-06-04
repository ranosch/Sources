LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = -x^3*y^2*z+x*y^4*z-x^3*y*z^2-x*y^3*z^2-x*y^2*z^3+x*y*z^4;
bfct(F);
tst_status(1);$
