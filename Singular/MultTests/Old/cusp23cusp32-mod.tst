LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),Dp;
poly F = (x2+y3)*(x3+y2);
bfct(F);
tst_status(1);$
