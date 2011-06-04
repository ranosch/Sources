LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(z,y,x),dp;
poly F = x^7*z-x*y^6*z+x^6*y-y^7;
bfct(F);
tst_status(1);$

