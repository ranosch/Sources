LIB"tst.lib";
tst_init();

ring r = (integer, 2, 30), (a, b, c, d), dp;
ideal I = 525389927*b*c^4+167555562*b*c^8,338903139*a*b*c^8,913440624*b*c^3*d+1000228536*b*c^3*d^6+1014963707*b^8*d^2,403582638*a*c^2*d^4+67999203*a*c^4*d^5;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d), dp;
ideal I = 518635746*d^6+47501302*c^7*d^2+879618936*a*b^4*c^4*d,479958711*b*d^2,250201515*a^3*b*c^3*d^3,178509225*c^7*d^3+696627097*b^4*d^3;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e), dp;
ideal I = 259375660*a*b*c^4*e^3+809583820*a^2*c*d*e^6+425304563*a^4*b^5*c,42982191*a*b^3*d*e^3,330954847*a^2*b^6*c*e+762950827*a^4*c*d^4,408042795*b^5*c^2*d*e+424031424*b^6*c*d+580811523*a*b*c^5*d^3+704279527*a*b^7*c,720313897*b^4*c^4+346633698*b^7*d^3+510328152*a*b*d^5+765860402*a*b^3*c^2*d*e^3+458497827*a^2*b^4*d*e^2;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e), dp;
ideal I = 286535155*b^5*c*e^4,217979819*b*c^2*d+258958045*b^2*c^2*d^2*e^2+888183556*a^2*d^2*e^3,976307840*c*d^4*e^4+389145335*a^2*b*d^6,788091568*a^2*b*c^4*d*e^2,249972210*d^5*e^2+1059819331*b^6*c^2+319770454*a^3*b^3*e;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e, f, g), dp;
ideal I = 133255505*a*c^2*d^2*g^3+477046826*a^3*c^2*d^2*f,726006854*b^2*c^2*e*f*g^2,414041330*a*d^7*g+579667919*a*b^5*c*e*g^2,609919471*a^2*b^2*c^3*d*e*g,911050118*d^2*e^4+594915497*b^4*c^2*d^2*g;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e, f, g), dp;
ideal I = 807519818*b*c^2*f*g^5+205010838*b*c^3*d*e^3+802447149*b^2*c^3*d*e^2*g,811734998*c*d^3*e^3*f^2*g+863985695*b^5*c^4*e,530517600*b^2*c^2*e^4*f^2,768279725*c^3*e*f^3*g^2+744418602*a^3*b^2*e^2*g^3,745704832*b*c^2*e*f^5*g+690642017*a^2*d^3*g^2;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e, f, g, h, i, j), dp;
ideal I = 590408825*d*f,426190262*f*j^3,119615159*c*g,821070688*e*g*i+973187654*d*e*g*j+449125849*d*e^2+282865404*c*e^2*j+962999595*b*c*h*i+1006951352*a*e*g*i,797314585*a*b*c*d,599278766*f*h^2*j,646476661*f*h+883119978*d*e^2*j,251173996*h*j+437043746*d^2*e^2,506298852*d*f^2*j,599498282*e^2*i*j;
ideal G = std(I);
G;
kill r;
ring r = (integer, 2, 30), (a, b, c, d, e, f, g, h, i, j), dp;
ideal I = 866261011*d*f*h*i,782535033*e*f^2*i+1010483722*a*g*i,742774253*c*e^2+1018297746*b*e*h*i+618320406*a*b*c*f,180951907*a*e^2*i,200558448*i*j+480254204*a*e*f*i,141400270*b*g^3+348525958*a*i*j+622305899*a*b*c*g,1051894207*e*g^2*i+401353768*b*f*g*j,445199166*b^2*c*j,664249637*d^2*h^2,525086704*d^2*f*i;
ideal G = std(I);
G;
kill r;

tst_status(1);$
