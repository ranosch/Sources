LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = xy7+y8+x6;
bfct(F);
tst_status(1);$
