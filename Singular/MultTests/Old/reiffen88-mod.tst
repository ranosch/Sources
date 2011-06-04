LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = x8+xy7+y8;
bfct(F);
tst_status(1);$
