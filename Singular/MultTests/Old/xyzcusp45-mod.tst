LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y,z),dp;
poly F = x*y^5*z+y^6+x^5*z+x^4*y;
bfct(F);
tst_status(1);$
