LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = x^4*z-x*y^3*z+x^3*y-y^4;
bfct(F);
tst_status(1);$
