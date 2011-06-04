LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = xy8+y9+x8;
bfct(F);
tst_status(1);$
