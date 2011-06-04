LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = y^9 + x^9 + x*y^8;
bfct(F);
tst_status(1);$
