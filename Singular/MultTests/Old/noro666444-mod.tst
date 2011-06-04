LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y,z),dp;
poly F = x^6 + y^6 + z^6 + x^4 * y^4 * z^4;
bfct(F);
tst_status(1);$
