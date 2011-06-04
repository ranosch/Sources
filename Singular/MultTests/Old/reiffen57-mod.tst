LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = xy6+y7+x5;
bfct(F);
tst_status(1);$
