LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = x^5*z-x*y^4*z+x^4*y-y^5;
bfct(F);
tst_status(1);$

