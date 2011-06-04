LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y),dp;
poly f1 = y5+x*y^4+x4;
poly f2 = x5+x^4*y+y4;
poly F = f1*f2;
bfct(F);
tst_status(1);$
