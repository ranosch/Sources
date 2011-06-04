LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = y^11 + x^11 + x*y^10;
bfct(F);
tst_status(1);$
