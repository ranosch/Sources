LIB "tst.lib";LIB "dmod.lib";
tst_init();
ring r = 0,(x,y),dp;
poly F = x5+xy4+y5;
bfct(F);
tst_status(1);$
