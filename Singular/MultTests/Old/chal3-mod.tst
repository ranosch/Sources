LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring R = 0,(x,y),dp;
poly f1 = x2+y^2*(1+y);
poly f2 = y3+x2;
poly F = f1*f2;
bfct(F);
tst_status(1);$
