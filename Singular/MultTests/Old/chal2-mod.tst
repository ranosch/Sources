LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y),dp;
poly f1 = x^3+y^2;
poly f2 = y^3+x^2;
poly F = f1*f2;
bfct(F);
tst_status(1);$
