// File: alexpoly.tst
// Tests for alexpoly lib
LIB "tst.lib";
tst_init();
LIB "alexpoly.lib";
ring r=0,(x,y),ds;
//////////////////////////////////////////////////////////////////////////
//  Defining examples.
//////////////////////////////////////////////////////////////////////////
//  Examples of polynomials
/////////////////////////////////////////////////////////////////////////
list f;
f[1] =x2-y2;
f[2] =x2+y+y2;
f[3] =(x2+y3)*(x2+y3+xy2);
f[4] =-x27-x25-15x24y-30x23y2+5x20y3-135x19y4+3x18y5-10x15y6-90x14y7+10x10y9-3x9y10-5x5y12+y15;
f[5] =x5-y11;
f[6] =xy8+y8+x4y6+4x3y6+2x5y5+6x6y4+4x8y3+x10y2+4x9y2+2x11y+x12;
f[7] =(x6-y4);
f[8] =(((y-x2+x3)*(y-x2-x3)));
f[9] =((x7-2x4y2+xy4-1y5)*(x7-4x4y2+4xy4-1y5));
f[10]=((y2-x3)*(y2-x3-x4));
f[11]=((y2-x3-x4)*(y2+x3+x4));
f[12]=(((x2-y)^2+x5)*((2x2-y)^2+x5));
f[13]=((x2-y4)*(x+y4));
f[14]=-x9+x8-6x7y+3x6y2-2x4y3-3x3y4+y6;
f[15]=-x21+x20-8x18y-4x15y2-8x13y3+6x10y4-4x5y6+y8;
f[16]=-x19+x18-12x17y-6x15y2-40x14y3+15x12y4-12x11y5-20x9y6+15x6y8-6x3y10+y12;
f[17]=x22-x21-14x20y+7x18y2-70x17y3-21x15y4-42x14y5+35x12y6-2x11y7-35x9y8+21x6y10-7x3y12+y14;
f[18]=-x17-2x16-x15-20x13y2+5x12y2-10x10y4-10x9y4+10x6y6-5x3y8+y10;
f[19]=(f[16]*f[17]*f[18]);
f[20]=((x2-y3)*(x3-y5)*(x5-y7)*(x7-y11)*(x11-y13));
f[21]=((x3+3x2y-xy4+y10)*(x3-x2y+y8));
f[22]=-x11+x10-4x8y-2x5y2+y4;
f[23]=x7-y8;
f[24]=x15-y16;
f[25]=f[1]*f[2];
f[26]=f[2]*f[3];
f[27]=f[4]*f[5];
f[28]=f[1]*f[2]*f[3]*f[4]*f[5];
f[29]=f[14]*f[15];
f[30]=f[6]*f[7];
f[31]=f[6]*f[8]*f[12];
f[32]=2x2+3xy+4xy3-x2y;
f[33]=(x-y)*(x-2y)*(x-3y)*(x-4y);
f[34]=(x-y)*(x-2y)*(x-3y)*(x-4y)*(x-5y);
f[35]=(x7-y3)*(y4-2x3y2-4x5y+x6-x7)*(x2-y11);
f[36]=-x23-2x22-x21-42x19y2+7x18y2-70x16y4-21x15y4-14x13y6+35x12y6-35x9y8+21x6y10-7x3y12+y14;
f[37]=-x29-x28+7x24y-21x20y2+35x16y3-35x12y4+21x8y5-7x4y6+y7;

poly p_1 = y2+x3;
poly p_2 = p_1^2 + x5y;
poly p_3 = p_2^2 + x^10 *p_1;
poly p_4 = p_3^2 + x^20 *p_2;
poly p_5 = p_4^2 + x^40 *p_3;

f[38]=p_1;
f[39]=p_2;
f[40]=p_3;
f[41]=p_4;
f[42]=p_5;
f[43]=p_1*p_2*p_3;
f[44]=p_3*p_5;

f[45]=(-x7+x6-4x5y-2x3y2+y4)*(-x21+x20-12x19y-30x17y2-4x15y3+3x14y4-48x12y5+6x10y6-3x7y8-4x5y9+y12);
f[46]=f[16]*f[17]*f[18]*f[22]*f[23]*f[24];
f[47]=(x5-y7)*(x10-y17);
f[48]=(x5-y7)*(x13-y23);
f[49]=(x5-y7)*(x4383-y5344);
f[50]=(x5-y7)*(x10-y17)*(x7-y11);

list f_irr=x-y,x+y,y-x2+x3,y2-x3-x4,(x2-y)^2+x5,(2x2-y)^2+x5,x-y2,x+y2,x+y4,x3-y5,x5-y7,x7-y11,x11-y13,f[2],f[4],f[5],f[6],f[14],f[15],f[16],f[17],f[18],f[22],f[23],f[24],f[36],f[37],f[38],f[39],f[40],f[41],f[42],(-x7+x6-4x5y-2x3y2+y4),(-x21+x20-12x19y-30x17y2-4x15y3+3x14y4-48x12y5+6x10y6-3x7y8-4x5y9+y12),(x10-y17),(x13-y23),x204-y1111,x4383-y5344;

///////////////////////////////////////////////////////////////////////////////////////////
// Defining the invariants of the above examples.
///////////////////////////////////////////////////////////////////////////////////////////
list FF;
//Polynomial: f[1]=x2-y2
FF[1]=list(intmat(intvec(0,1,1,0),2,2),list(intvec(1),intvec(1)));
//Polynomial: f[2]=y+x2+y2
FF[2]=list(intmat(intvec(0),1,1),list(intvec(1)));
//Polynomial: f[3]=x4+x3y2+2x2y3+xy5+y6
FF[3]=list(intmat(intvec(0,4,4,0),2,2),list(intvec(2,3),intvec(2,3)));
//Polynomial: f[4]=y15-5x5y12+10x10y9-3x9y10-10x15y6-90x14y7+5x20y3-135x19y4+3x18y5-x25-15x24y-30x23y2-x27
FF[4]=list(intmat(intvec(0),1,1),list(intvec(15,25,27)));
//Polynomial: f[5]=x5-y11
FF[5]=list(intmat(intvec(0),1,1),list(intvec(5,11)));
//Polynomial: f[6]=y8+4x3y6+xy8+6x6y4+2x5y5+x4y6+4x9y2+4x8y3+x12+2x11y+x10y2
FF[6]=list(intmat(intvec(0),1,1),list(intvec(8,12,14,15)));
//Polynomial: f[7]=-y4+x6
FF[7]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(2,3),intvec(2,3)));
//Polynomial: f[8]=y2-2x2y+x4-x6
FF[8]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(1),intvec(1)));
//Polynomial: f[9]=4x2y8-5xy9+y10-12x5y6+6x4y7+13x8y4-2x7y5-6x11y2+x14
FF[9]=list(intmat(intvec(0,1,1,1,1,0,1,1,1,1,0,3,1,1,3,0),4,4),list(intvec(1),intvec(1),intvec(4,6,7),intvec(4,6,7)));
//Polynomial: f[10]=y4-2x3y2+x6-x4y2+x7
FF[10]=list(intmat(intvec(0,5,5,0),2,2),list(intvec(2,3),intvec(2,3)));
//Polynomial: f[11]=y4-x6-2x7-x8
FF[11]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(2,3),intvec(2,3)));
//Polynomial: f[12]=y4-6x2y3+13x4y2-12x6y+2x5y2+4x8-6x7y+5x9+x10
FF[12]=list(intmat(intvec(0,2,2,0),2,2),list(intvec(2,5),intvec(2,5)));
//Polynomial: f[13]=x3-xy4+x2y4-y8
FF[13]=list(intmat(intvec(0,2,2,2,0,2,2,2,0),3,3),list(intvec(1),intvec(1),intvec(1)));
//Polynomial: f[14]=y6-2x4y3-3x3y4+x8-6x7y+3x6y2-x9
FF[14]=list(intmat(intvec(0),1,1),list(intvec(6,8,9)));
//Polynomial: f[15]=y8-4x5y6+6x10y4-8x13y3-4x15y2-8x18y+x20-x21
FF[15]=list(intmat(intvec(0),1,1),list(intvec(8,20,21)));
//Polynomial: f[16]=y12-6x3y10+15x6y8-20x9y6+15x12y4-12x11y5-6x15y2-40x14y3+x18-12x17y-x19
FF[16]=list(intmat(intvec(0),1,1),list(intvec(12,18,19)));
//Polynomial: f[17]=y14-7x3y12+21x6y10-35x9y8+35x12y6-2x11y7-21x15y4-42x14y5+7x18y2-70x17y3-x21-14x20y+x22
FF[17]=list(intmat(intvec(0),1,1),list(intvec(14,21,22)));
//Polynomial: f[18]=y10-5x3y8+10x6y6-10x9y4+5x12y2-10x10y4-x15-20x13y2-2x16-x17
FF[18]=list(intmat(intvec(0),1,1),list(intvec(10,15,17)));
//Polynomial: f[19]
FF[19]=list(intmat(intvec(0,9,6,9,0,6,6,6,0),3,3),list(intvec(14,21,22),intvec(12,18,19),intvec(10,15,17)));
//Polynomial: f[20]
FF[20]=list(intmat(intvec(0,4,3,3,3,4,0,3,3,3,3,3,0,3,3,3,3,3,0,4,3,3,3,4,0),5,5),list(intvec(11,13),intvec(5,7),intvec(2,3),intvec(7,11),intvec(3,5)));
//Polynomial: f[21]=x6+2x5y-3x4y2-x4y4+x3y5+x3y8+3x2y9+x3y10-x2y11-xy12+y18
FF[21]=list(intmat(intvec(0,1,1,1,1,1,0,1,1,1,1,1,0,3,3,1,1,3,0,4,1,1,3,4,0),5,5),list(intvec(1),intvec(1),intvec(1),intvec(2,7),intvec(1)));
//Polynomial: f[22]=y4-2x5y2-4x8y+x10-x11
FF[22]=list(intmat(intvec(0),1,1),list(intvec(4,10,11)));
//Polynomial: f[23]=x7-y8
FF[23]=list(intmat(intvec(0),1,1),list(intvec(7,8)));
//Polynomial: f[24]=x15-y16
FF[24]=list(intmat(intvec(0),1,1),list(intvec(15,16)));
//Polynomial: f[25]=x2y-y3+x4-y4
FF[25]=list(intmat(intvec(0,1,1,1,0,1,1,1,0),3,3),list(intvec(1),intvec(1),intvec(1)));
//Polynomial: f[26]=x4y+x6+x4y2+x3y3+2x2y4+x5y2+2x4y3+x3y4+2x2y5+xy6+y7+x3y5+x2y6+xy7+y8
FF[26]=list(intmat(intvec(0,1,1,1,0,4,1,4,0),3,3),list(intvec(1),intvec(2,3),intvec(2,3)));
//Polynomial: f[27]
FF[27]=list(intmat(intvec(0,1,1,0),2,2),list(intvec(15,25,27),intvec(5,11)));
//Polynomial: f[28]
FF[28]=list(intmat(intvec(0,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,0,2,1,1,1,1,1,2,0,1,1,1,1,1,1,1,0,4,2,1,1,1,1,4,0,2,1,1,1,1,2,2,0),7,7),list(intvec(1),intvec(1),intvec(15,25,27),intvec(1),intvec(2,3),intvec(2,3),intvec(5,11)));
//Polynomial: f[29]
FF[29]=list(intmat(intvec(0,2,2,0),2,2),list(intvec(6,8,9),intvec(8,20,21)));
//Polynomial: f[30]=-y12-4x3y10-xy12-5x6y8-2x5y9-x4y10-4x8y7+x7y8+5x12y4+4x15y2+4x14y3+x18+2x17y+x16y2
FF[30]=list(intmat(intvec(0,3,3,3,0,4,3,4,0),3,3),list(intvec(2,3),intvec(2,3),intvec(8,12,14,15)));
//Polynomial: f[31]
FF[31]=list(intmat(intvec(0,2,2,2,2,2,0,2,2,2,2,2,0,3,3,2,2,3,0,3,2,2,3,3,0),5,5),list(intvec(8,12,14,15),intvec(2,5),intvec(2,5),intvec(1),intvec(1)));
//Polynomial: f[32]=2x2+3xy-x2y+4xy3
FF[32]=list(intmat(intvec(0,1,1,0),2,2),list(intvec(1),intvec(1)));
//Polynomial: f[33]=x4-10x3y+35x2y2-50xy3+24y4
FF[33]=list(intmat(intvec(0,1,1,1,1,0,1,1,1,1,0,1,1,1,1,0),4,4),list(intvec(1),intvec(1),intvec(1),intvec(1)));
//Polynomial: f[34]=x5-15x4y+85x3y2-225x2y3+274xy4-120y5
FF[34]=list(intmat(intvec(0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0),5,5),list(intvec(1),intvec(1),intvec(1),intvec(1),intvec(1)));
//Polynomial: f[35]
FF[35]=list(intmat(intvec(0,2,1,2,0,1,1,1,0),3,3),list(intvec(4,6,7),intvec(3,7),intvec(2,11)));
//Polynomial: f[36]=y14-7x3y12+21x6y10-35x9y8+35x12y6-21x15y4-14x13y6+7x18y2-70x16y4-x21-42x19y2-2x22-x23
FF[36]=list(intmat(intvec(0),1,1),list(intvec(14,21,23)));
//Polynomial: f[37]=y7-7x4y6+21x8y5-35x12y4+35x16y3-21x20y2+7x24y-x28-x29
FF[37]=list(intmat(intvec(0),1,1),list(intvec(7,29)));
//Polynomial: f[38]=y2+x3
FF[38]=list(intmat(intvec(0),1,1),list(intvec(2,3)));
//Polynomial: f[39]=y4+2x3y2+x6+x5y
FF[39]=list(intmat(intvec(0),1,1),list(intvec(4,6,7)));
//Polynomial: f[40]=y8+4x3y6+6x6y4+2x5y5+4x9y2+4x8y3+x12+2x11y+2x10y2+x13
FF[40]=list(intmat(intvec(0),1,1),list(intvec(8,12,14,15)));
//Polynomial: f[41]
FF[41]=list(intmat(intvec(0),1,1),list(intvec(16,24,28,30,31)));
//Polynomial: f[42]
FF[42]=list(intmat(intvec(0),1,1),list(intvec(32,48,56,60,62,63)));
//Polynomial: f[43]
FF[43]=list(intmat(intvec(0,4,4,4,0,6,4,6,0),3,3),list(intvec(2,3),intvec(8,12,14,15),intvec(4,6,7)));
//Polynomial: f[44]
FF[44]=list(intmat(intvec(0,8,8,0),2,2),list(intvec(32,48,56,60,62,63),intvec(8,12,14,15)));
//Polynomial: f[45]
FF[45]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(4,6,7),intvec(12,20,21)));
//Polynomial: f[46]
FF[46]=list(intmat(intvec(0,1,1,2,2,2,1,0,8,1,1,1,1,8,0,1,1,1,2,1,1,0,9,6,2,1,1,9,0,6,2,1,1,6,6,0),6,6),list(intvec(4,10,11),intvec(7,8),intvec(15,16),intvec(12,18,19),intvec(14,21,22),intvec(10,15,17)));
//Polynomial: f[47]=(x5-y7)(x10-y17)
FF[47]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(5,7),intvec(10,17)));
//Polynomial: f[48]=(x5-y7)(x13-y23)
FF[48]=list(intmat(intvec(0,3,3,0),2,2),list(intvec(5,7),intvec(13,23)));
//Polynomial: f[49]=(x5-y7)(x4383-y5344)
FF[49]=list(intmat(intvec(0,4,4,0),2,2),list(intvec(5,7),intvec(4383,5344)));
//Polynomial: f[50]=(x5-y7)(x10-y17)(x7-y11)
FF[50]=list(intmat(intvec(0,3,3,3,0,4,3,4,0),3,3),list(intvec(5,7),intvec(10,17),intvec(7,11)));
//Polynomial: f[51]=f[4]*(x2+y3)*f[5];
FF[51]=list(intmat(intvec(0,1,1,1,0,2,1,2,0),3,3),list(intvec(15,25,27),intvec(2,3),intvec(5,11)));

//////////////////////////////////////////////////////////////////////////////////////
/// Examples, created from f_irr 
//////////////////////////////////////////////////////////////////////////////////////
// Consider the product of all the polynomials in f_irr.
// Polynomial: (x-y) (x+y) (y-x2+x3) (y2-x3-x4) (y2-2x2y+x4+x5) (y2-4x2y+4x4+x5) (x-y2) (x+y2) (x+y4) (x3-y5) (x5-y7) (x7-y11) (x11-y13) (y+x2+y2) (y15-5x5y12+10x10y9-3x9y10-10x15y6-90x14y7+5x20y3-135x19y4+3x18y5-x25-15x24y-30x23y2-x27) (x5-y11) (y8+4x3y6+xy8+6x6y4+2x5y5+x4y6+4x9y2+4x8y3+x12+2x11y+x10y2) (y6-2x4y3-3x3y4+x8-6x7y+3x6y2-x9) (y8-4x5y6+6x10y4-8x13y3-4x15y2-8x18y+x20-x21) (y12-6x3y10+15x6y8-20x9y6+15x12y4-12x11y5-6x15y2-40x14y3+x18-12x17y-x19) (y14-7x3y12+21x6y10-35x9y8+35x12y6-2x11y7-21x15y4-42x14y5+7x18y2-70x17y3-x21-14x20y+x22) (y10-5x3y8+10x6y6-10x9y4+5x12y2-10x10y4-x15-20x13y2-2x16-x17) (y4-2x5y2-4x8y+x10-x11) (x7-y8) (x15-y16) (y14-7x3y12+21x6y10-35x9y8+35x12y6-21x15y4-14x13y6+7x18y2-70x16y4-x21-42x19y2-2x22-x23) (y7-7x4y6+21x8y5-35x12y4+35x16y3-21x20y2+7x24y-x28-x29) (y2+x3) (y4+2x3y2+x6+x5y) (y8+4x3y6+6x6y4+2x5y5+4x9y2+4x8y3+x12+2x11y+2x10y2+x13) (y16+8x3y14+28x6y12+4x5y13+56x9y10+24x8y11+70x12y8+60x11y9+8x10y10+56x15y6+80x14y7+34x13y8+28x18y4+60x17y5+56x16y6+8x15y7+8x21y2+24x20y3+44x19y4+20x18y5+x24+4x23y+16x22y2+16x21y3+5x20y4+2x25+4x24y+6x23y2+2x26+x25y) (y32+16x3y30+120x6y28+8x5y29+560x9y26+112x8y27+1820x12y24+728x11y25+32x10y26+4368x15y22+2912x14y23+388x13y24+8008x18y20+8008x17y21+2160x16y22+80x15y23+11440x21y18+16016x20y19+7304x19y20+824x18y21+12870x24y16+24024x23y17+16720x22y18+3840x21y19+138x20y20+11440x27y14+27456x26y15+27324x25y16+10680x24y17+1180x23y18+8008x30y12+24024x29y13+32736x28y14+19680x27y15+4480x26y16+170x25y17+4368x33y10+16016x32y11+29040x31y12+25200x30y13+9920x29y14+1168x28y15+1820x36y8+8008x35y9+19008x34y10+22848x33y11+14140x32y12+3472x31y13+152x30y14+560x39y6+2912x38y7+9020x37y8+14640x36y9+13496x35y10+5824x34y11+804x33y12+120x42y4+728x41y5+2992x40y6+6480x39y7+8680x38y8+6020x37y9+1776x36y10+96x35y11+16x45y2+112x44y3+648x43y4+1880x42y5+3680x41y6+3920x40y7+2112x39y8+364x38y9+x48+8x47y+80x46y2+320x45y3+970x44y4+1568x43y5+1448x42y6+544x41y7+42x40y8+4x49+24x48y+140x47y2+352x46y3+564x45y4+400x44y5+104x43y6+8x50+34x49y+112x48y2+144x47y3+94x46y4+12x45y5+8x51+20x50y+36x49y2+16x48y3+5x52+6x51y+3x50y2+x53) (y4-2x3y2+x6-4x5y-x7) (y12-4x5y9-3x7y8+6x10y6-48x12y5-4x15y3+3x14y4-30x17y2+x20-12x19y-x21) (x10-y17) (x13-y23) (x204-y1111) (x4383-y5344)
FF[52]=list(intmat(intvec(0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2,3,2,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,2,0,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,4,4,4,2,1,1,4,2,3,3,3,3,3,4,3,1,1,1,1,1,1,3,2,0,2,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,2,2,2,0,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,0,2,2,2,2,2,2,1,1,2,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,2,0,2,2,2,2,2,1,1,2,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,2,2,0,2,2,2,2,1,1,3,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,2,4,2,1,1,1,1,1,1,2,2,2,0,3,4,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,4,4,2,3,1,1,1,1,1,1,2,2,2,3,0,3,4,1,1,2,1,1,1,1,1,1,1,4,4,1,1,1,1,1,1,1,1,1,3,3,2,4,1,1,1,1,1,1,2,2,2,4,3,0,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,4,4,2,3,1,1,1,1,1,1,2,2,2,3,4,3,0,1,1,2,1,1,1,1,1,1,1,7,7,1,1,1,1,1,1,1,1,1,3,3,2,6,1,1,2,2,2,2,1,1,1,1,1,1,1,0,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,0,1,3,3,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,7,1,1,1,1,1,1,1,1,1,1,2,2,3,2,2,2,2,1,1,0,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,2,3,2,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,0,3,2,3,3,3,2,1,1,3,2,4,6,7,7,7,3,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,3,0,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,3,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,0,2,2,2,6,1,1,2,3,2,2,2,2,2,2,2,1,1,1,1,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,0,9,6,2,1,1,7,2,3,3,3,3,3,5,3,1,1,1,1,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,9,0,6,2,1,1,7,2,3,3,3,3,3,5,3,1,1,1,1,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,6,6,0,2,1,1,6,2,3,3,3,3,3,5,3,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,6,2,2,2,0,1,1,2,3,2,2,2,2,2,2,2,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,3,7,1,1,2,1,1,1,1,1,1,1,0,8,1,1,1,1,1,1,1,1,1,3,3,2,6,1,1,1,1,1,1,2,2,2,3,4,3,7,1,1,2,1,1,1,1,1,1,1,8,0,1,1,1,1,1,1,1,1,1,3,3,2,6,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,7,7,6,2,1,1,0,2,3,3,3,3,3,5,3,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,3,2,2,2,3,1,1,2,0,2,2,2,2,2,2,2,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,4,3,2,3,3,3,2,1,1,3,2,0,4,4,4,4,3,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,6,3,2,3,3,3,2,1,1,3,2,4,0,6,6,6,3,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,0,8,8,3,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,8,0,10,3,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,8,10,0,3,3,1,1,1,1,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,5,5,5,2,1,1,5,2,3,3,3,3,3,0,3,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,7,1,3,3,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,0,1,1,1,1,1,1,1,1,1,1,2,2,2,4,3,4,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,0,5,2,3,1,1,1,1,1,1,2,2,2,4,3,4,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,5,0,2,3,1,1,1,1,1,1,2,2,4,2,2,2,2,1,1,3,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,2,2,0,2,1,1,1,1,1,1,2,2,2,3,4,3,6,1,1,2,1,1,1,1,1,1,1,6,6,1,1,1,1,1,1,1,1,1,3,3,2,0),38,38),list(intvec(1),intvec(1),intvec(1),intvec(2,3),intvec(2,5),intvec(2,5),intvec(1),intvec(1),intvec(1),intvec(3,5),intvec(5,7),intvec(7,11),intvec(11,13),intvec(1),intvec(15,25,27),intvec(5,11),intvec(8,12,14,15),intvec(6,8,9),intvec(8,20,21),intvec(12,18,19),intvec(14,21,22),intvec(10,15,17),intvec(4,10,11),intvec(7,8),intvec(15,16),intvec(14,21,23),intvec(7,29),intvec(2,3),intvec(4,6,7),intvec(8,12,14,15),intvec(16,24,28,30,31),intvec(32,48,56,60,62,63),intvec(4,6,7),intvec(12,20,21),intvec(10,17),intvec(13,23),intvec(204,1111),intvec(4383,5344)));

// Polynomial : as in FF[52] without the last four polynomials: (x-y) (x+y) (y-x2+x3) (y2-x3-x4) (y2-2x2y+x4+x5) (y2-4x2y+4x4+x5) (x-y2) (x+y2) (x+y4) (x3-y5) (x5-y7) (x7-y11) (x11-y13) (y+x2+y2) (y15-5x5y12+10x10y9-3x9y10-10x15y6-90x14y7+5x20y3-135x19y4+3x18y5-x25-15x24y-30x23y2-x27) (x5-y11) (y8+4x3y6+xy8+6x6y4+2x5y5+x4y6+4x9y2+4x8y3+x12+2x11y+x10y2) (y6-2x4y3-3x3y4+x8-6x7y+3x6y2-x9) (y8-4x5y6+6x10y4-8x13y3-4x15y2-8x18y+x20-x21) (y12-6x3y10+15x6y8-20x9y6+15x12y4-12x11y5-6x15y2-40x14y3+x18-12x17y-x19) (y14-7x3y12+21x6y10-35x9y8+35x12y6-2x11y7-21x15y4-42x14y5+7x18y2-70x17y3-x21-14x20y+x22) (y10-5x3y8+10x6y6-10x9y4+5x12y2-10x10y4-x15-20x13y2-2x16-x17) (y4-2x5y2-4x8y+x10-x11) (x7-y8) (x15-y16) (y14-7x3y12+21x6y10-35x9y8+35x12y6-21x15y4-14x13y6+7x18y2-70x16y4-x21-42x19y2-2x22-x23) (y7-7x4y6+21x8y5-35x12y4+35x16y3-21x20y2+7x24y-x28-x29) (y2+x3) (y4+2x3y2+x6+x5y) (y8+4x3y6+6x6y4+2x5y5+4x9y2+4x8y3+x12+2x11y+2x10y2+x13) (y16+8x3y14+28x6y12+4x5y13+56x9y10+24x8y11+70x12y8+60x11y9+8x10y10+56x15y6+80x14y7+34x13y8+28x18y4+60x17y5+56x16y6+8x15y7+8x21y2+24x20y3+44x19y4+20x18y5+x24+4x23y+16x22y2+16x21y3+5x20y4+2x25+4x24y+6x23y2+2x26+x25y) (y32+16x3y30+120x6y28+8x5y29+560x9y26+112x8y27+1820x12y24+728x11y25+32x10y26+4368x15y22+2912x14y23+388x13y24+8008x18y20+8008x17y21+2160x16y22+80x15y23+11440x21y18+16016x20y19+7304x19y20+824x18y21+12870x24y16+24024x23y17+16720x22y18+3840x21y19+138x20y20+11440x27y14+27456x26y15+27324x25y16+10680x24y17+1180x23y18+8008x30y12+24024x29y13+32736x28y14+19680x27y15+4480x26y16+170x25y17+4368x33y10+16016x32y11+29040x31y12+25200x30y13+9920x29y14+1168x28y15+1820x36y8+8008x35y9+19008x34y10+22848x33y11+14140x32y12+3472x31y13+152x30y14+560x39y6+2912x38y7+9020x37y8+14640x36y9+13496x35y10+5824x34y11+804x33y12+120x42y4+728x41y5+2992x40y6+6480x39y7+8680x38y8+6020x37y9+1776x36y10+96x35y11+16x45y2+112x44y3+648x43y4+1880x42y5+3680x41y6+3920x40y7+2112x39y8+364x38y9+x48+8x47y+80x46y2+320x45y3+970x44y4+1568x43y5+1448x42y6+544x41y7+42x40y8+4x49+24x48y+140x47y2+352x46y3+564x45y4+400x44y5+104x43y6+8x50+34x49y+112x48y2+144x47y3+94x46y4+12x45y5+8x51+20x50y+36x49y2+16x48y3+5x52+6x51y+3x50y2+x53) (y4-2x3y2+x6-4x5y-x7) (y12-4x5y9-3x7y8+6x10y6-48x12y5-4x15y3+3x14y4-30x17y2+x20-12x19y-x21) 
FF[53]=list(intmat(intvec(0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,2,3,2,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,2,0,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,4,4,4,2,1,1,4,2,3,3,3,3,3,4,3,1,1,3,2,0,2,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,2,2,2,0,1,1,1,1,1,1,1,2,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,1,1,1,1,0,2,2,2,2,2,2,1,1,2,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,0,2,2,2,2,2,1,1,2,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,0,2,2,2,2,1,1,3,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,0,3,4,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,0,3,4,1,1,2,1,1,1,1,1,1,1,4,4,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,4,3,0,3,1,1,2,1,1,1,1,1,1,1,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,3,0,1,1,2,1,1,1,1,1,1,1,7,7,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,1,1,1,1,1,1,1,0,2,1,2,2,2,2,2,2,2,1,1,2,2,2,2,2,2,2,2,2,1,1,2,3,2,2,1,1,1,1,1,1,1,2,0,1,3,3,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,7,1,1,1,1,1,1,2,2,3,2,2,2,2,1,1,0,1,1,1,1,1,1,1,2,2,1,1,1,1,1,1,1,1,1,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,0,3,2,3,3,3,2,1,1,3,2,4,6,7,7,7,3,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,3,0,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,3,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,0,2,2,2,6,1,1,2,3,2,2,2,2,2,2,2,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,0,9,6,2,1,1,7,2,3,3,3,3,3,5,3,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,9,0,6,2,1,1,7,2,3,3,3,3,3,5,3,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,6,6,0,2,1,1,6,2,3,3,3,3,3,5,3,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,6,2,2,2,0,1,1,2,3,2,2,2,2,2,2,2,1,1,1,1,1,1,2,2,2,3,4,3,7,1,1,2,1,1,1,1,1,1,1,0,8,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,3,4,3,7,1,1,2,1,1,1,1,1,1,1,8,0,1,1,1,1,1,1,1,1,1,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,7,7,6,2,1,1,0,2,3,3,3,3,3,5,3,1,1,2,2,2,2,1,1,1,1,1,1,1,2,2,1,2,2,3,2,2,2,3,1,1,2,0,2,2,2,2,2,2,2,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,4,3,2,3,3,3,2,1,1,3,2,0,4,4,4,4,3,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,6,3,2,3,3,3,2,1,1,3,2,4,0,6,6,6,3,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,0,8,8,3,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,8,0,10,3,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,3,1,7,3,2,3,3,3,2,1,1,3,2,4,6,8,10,0,3,3,1,1,2,4,2,2,1,1,1,1,1,1,1,2,3,1,3,3,2,5,5,5,2,1,1,5,2,3,3,3,3,3,0,3,1,1,2,3,2,2,1,1,1,1,1,1,1,2,7,1,3,3,2,3,3,3,2,1,1,3,2,3,3,3,3,3,3,0 ),34,34),list(intvec(1),intvec(1),intvec(1),intvec(2,3),intvec(2,5),intvec(2,5),intvec(1),intvec(1),intvec(1),intvec(3,5),intvec(5,7),intvec(7,11),intvec(11,13),intvec(1),intvec(15,25,27),intvec(5,11),intvec(8,12,14,15),intvec(6,8,9),intvec(8,20,21),intvec(12,18,19),intvec(14,21,22),intvec(10,15,17),intvec(4,10,11),intvec(7,8),intvec(15,16),intvec(14,21,23),intvec(7,29),intvec(2,3),intvec(4,6,7),intvec(8,12,14,15),intvec(16,24,28,30,31),intvec(32,48,56,60,62,63),intvec(4,6,7),intvec(12,20,21)));

//Polynomial: f[54]=f_irr[26]*f_irr[27]*f_irr[28]*f_irr[29];
FF[54]=list(intmat(intvec(0,2,3,3,2,0,2,2,3,2,0,4,3,2,4,0),4,4),list(intvec(14,21,23),intvec(7,29),intvec(2,3),intvec(4,6,7)));

/////////////////////////////////////////////////////////////////////////////////////
/// Examples of characteristic exponents
/////////////////////////////////////////////////////////////////////////////////////
list vv;
vv[1]=intvec(18,27,75,125);
vv[2]=intvec(27,36,60,100);
vv[3]=intvec(2,3);
vv[4]=intvec(3,7);
vv[5]=intvec(4,6,7);
vv[6]=intvec(5,8);
vv[7]=intvec(6,15,19);
vv[8]=intvec(7,16);
vv[9]=intvec(8,12,30,34);
vv[10]=intvec(9,21,23);
vv[11]=intvec(10,35,41);
vv[12]=intvec(30,115,1001);
vv[13]=intvec(100,150,375,420,672);
vv[14]=intvec(8,20,30,31);

/////////////////////////////////////////////////////////////////////////////////////
/// Examples of multiplicity sequences
/////////////////////////////////////////////////////////////////////////////////////
list w;
w[1]=intvec(2,1,1);
w[2]=intvec(3,3,1,1,1);
w[3]=intvec(4,2,2,1,1);
w[4]=intvec(5,3,2,1,1);
w[5]=intvec(6,6,3,3,3,1,1,1);
w[6]=intvec(7,7,2,2,2,1,1);
w[7]=intvec(8,4,4,4,4,4,4,2,2,2,2);
w[8]=intvec(9,9,3,3,3,2,1,1);
w[9]=intvec(10,10,10,5,5,5,1,1,1,1,1);
w[10]=intvec(30,30,30,25,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,1,1,1,1,1);
w[11]=intvec(100,50,50,50,50,50,50,25,25,25,20,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,2,2,1,1);
w[12]=intvec(8,8,4,4,4,4,2,2,1,1);
w[13]=intvec(18,9,9,9,9,9,9,9,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,1,1);
w[14]=intvec(27,9,9,9,9,9,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1);
w[15]=intvec(36,9,9,9,9,9,9,9,9,9,9,9,9,9,9,9,6,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1);
w[16]=intvec(21,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,2,1,1);

// ------------ test of resolutiongraph: -------------------
resolutiongraph(f[1]);
resolutiongraph(f[2]);
list Hne=develop(f[6]);
resolutiongraph(Hne);
resolutiongraph(f[36]);
resolutiongraph(FF[37]);
intvec v=6,9,16;
resolutiongraph(v);
intmat M1[2][2]=0,3,3,0;
intvec v1=2,3;
intvec v2=4,6,7;
list vectors=v1,v2;
list L1=M1,vectors;
resolutiongraph(L1);
intmat M2[3][3]=0,2,4,2,0,2,4,2,0;
intvec u1=6,8,9;
intvec u2=6,14,15;
intvec u3=8,10,11;
resolutiongraph(list(M2,list(u1,u2,u3)));
// ------------ test of totalmultiplicities and proximitymatrix: -------------------
totalmultiplicities(f[7]);
totalmultiplicities(hnexpansion(f[8]));
totalmultiplicities(f[9]);
totalmultiplicities(f[14]*f[15]);
totalmultiplicities(f[16]*f[17]*f[18]);
intmat m1[2][2]=0,10,10,0;
intvec v3=9,10;
intvec v4=10,11;
list L2=m1,list(v3,v4);
totalmultiplicities(L2);
intmat M3[3][3]=0,4,5,4,0,4,5,4,0;
intvec z1=21,28,36;
intvec z2=25,30,33;
intvec z3=24,32,35;
totalmultiplicities(list(M2,list(z1,z2,z3)));
list TM;
for (int i=1;i<=52;i++)
{
  TM[i]=totalmultiplicities(FF[i]);
  TM[i];
  proximitymatrix(TM[i][1]);
}
// ------------ test of alexanderpolynomial: -------------------
list ALEX=alexanderpolynomial(f[22]*f[23]);
def ALEXring=ALEX[1];
setring ALEXring;
alexpoly;
zeta_monodromy;
alexnumerator;
alexdenominator;
setring r;
kill ALEXring;
ALEX=alexanderpolynomial(f[22]*f[23]*f[24]);
def ALEXring=ALEX[1];
setring ALEXring;
alexpoly;
zeta_monodromy;
alexnumerator;
alexdenominator;
setring r;
kill ALEXring;
intvec vvv=18,27,30,31;
ALEX=alexanderpolynomial(vvv);
def ALEXring=ALEX[1];
setring ALEXring;
alexpoly;
zeta_monodromy;
alexnumerator;
alexdenominator;
setring r;
kill ALEXring;
ALEX=alexanderpolynomial(hnexpansion(f[4]*f[5]));
def ALEXring=ALEX[1];
setring ALEXring;
alexpoly;
zeta_monodromy;
alexnumerator;
alexdenominator;
setring r;
kill ALEXring;
// ------------ test of semigroup:  ------------------
semigroup(intvec(18,27,75,125));
semigroup(f[24]);
for (i=1;i<=52;i++)
{
  semigroup(FF[i]);
}
// ------------ test of charexp2multseq:  ------------------
for (i=1;i<=14;i++)
{
  charexp2multseq(vv[i]);
}
// ------------ test of charexp2generators: ------------------------
for (i=1;i<=14;i++)
{
  charexp2generators(vv[i]);
}
// ------------ test of charexp2inter: ------------------------
charexp2inter(intmat(intvec(0,1,1,0),2,2),list(vv[3],vv[4]));
charexp2inter(intmat(intvec(0,4,4,0),2,2),list(vv[2],vv[4]));
charexp2inter(intmat(intvec(0,1,3,1,0,2,3,2,0),2,2),list(vv[13],vv[4],vv[9]));
// ------------ test of charexp2conductor: ------------------------
for (i=1;i<=14;i++)
{
  charexp2conductor(vv[i]);
}
// ------------ test of multseq2charexp: ------------------------
for (i=1;i<=16;i++)
{
  multseq2charexp(w[i]);
}
// ------------ test of charexp2poly: -------------------
intvec a1=30,45,50,53;
vector b1=[1,1,1];
charexp2poly(a1,b1);
intvec a2=24,40,60,180,181;
vector b2=[1,1,1,1];
charexp2poly(a2,b2);
intvec a3=80,120,300,301;
vector b3=[1,1,1];
charexp2poly(a3,b3);
// ------------ test of tau_es2 --------------------------
for (i=2;i<=20;i++)
{
  tau_es2(x^2-y^i);
}
for (i=2;i<=10;i++)
{
  tau_es2(hnexpansion(y*(x^2-y^i)));
}
for (i=1;i<=size(FF)-1;i++)
{
  tau_es2(FF[i]);
}
tau_es2(a1);
// --------------- additions: -----------------------------
example resolutiongraph;
example totalmultiplicities;
example alexanderpolynomial;
example semigroup;
example proximitymatrix;
example charexp2multseq;
example multseq2charexp;
example charexp2generators;
example charexp2inter;
example charexp2conductor;
example charexp2poly;
example tau_es2;
// --------------------------------------------------------
tst_status(1);$
