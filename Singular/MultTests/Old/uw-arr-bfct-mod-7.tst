LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = x^2*y^3*z-x*y^3*z^2-x^2*y*z^3+x*y*z^4;
bfct(F);
tst_status(1);$
