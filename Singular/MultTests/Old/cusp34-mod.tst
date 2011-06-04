LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),Dp;
poly F = (x3+y4);
bfct(F);
tst_status(1);$
