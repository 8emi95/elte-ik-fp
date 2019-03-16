%baseclass-preinclude "semantics.h"

%lsp-needed

%token <szoveg> SZAMKONSTANS
%token PROGRAM
%token VALTOZOK
%token UTASITASOK
%token PROGRAM_VEGE
%token HA
%token AKKOR
%token KULONBEN
%token HA_VEGE
%token CIKLUS
%token AMIG
%token CIKLUS_VEGE
%token BE
%token KI
%token EGESZ
%token LOGIKAI
%token ERTEKADAS
%token BALZAROJEL
%token JOBBZAROJEL
%token <szoveg> AZONOSITO
%token IGAZ
%token HAMIS
%token SKIP

%token <szoveg> IDOKONST
%token IDO
%token PERC
%token ORA

%left VAGY
%left ES
%left NEM
%left EGYENLO
%left KISEBB NAGYOBB
%left PLUSZ MINUSZ
%left SZORZAS OSZTAS MARADEK

%type <kif> kifejezes
%type <utasitas> ertekadas
%type <utasitas> be
%type <utasitas> ki
%type <utasitas> elagazas
%type <utasitas> ciklus
%type <utasitas> utasitas
%type <utasitas> utasitasok
%type <utasitas> utasitaslista
%type <utasitas> deklaracio
%type <utasitas> deklaraciok
%type <utasitas> valtozolista
%type <utasitas> kezdes
%type <utasitas> befejezes

%union
{
    std::string *szoveg;
    kifejezes_leiro *kif;
    utasitas_leiro *utasitas;
}

%%

start:
    kezdes deklaraciok utasitasok befejezes
    {
        std::cout << $1->kod + $2->kod + $3->kod + $4->kod;
        delete $1;
        delete $2;
        delete $3;
        delete $4;
    }
;

kezdes:
    PROGRAM AZONOSITO
    {
        $$ = new utasitas_leiro( 0, 
            std::string("extern be_egesz\n") + "extern be_logikai\n"
            + "extern ki_egesz\n" + "extern ki_logikai\n"
            + "global main\n" );
    }
;

befejezes:
    PROGRAM_VEGE
    {
        $$ = new utasitas_leiro( d_loc__.first_line, "ret\n" );
    }
;

deklaraciok:
    // ures
    {
        $$ = new utasitas_leiro( 0, "" );
    }
|
    VALTOZOK valtozolista
    {
        $$ = new utasitas_leiro( d_loc__.first_line, 
            "section .bss\n" + $2->kod );
        delete $2;
    }
;

valtozolista:
    deklaracio
|
    deklaracio valtozolista
    {
        $$ = new utasitas_leiro( $1->sor, $1->kod + $2->kod );
        delete $1;
        delete $2;
    }
;

deklaracio:
    EGESZ AZONOSITO
    {
        if( szimb_tabla.count(*$2) > 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$2 << "' valtozo mar definialva volt a "
            << szimb_tabla[*$2].def_sora << ". sorban." << std::endl;
            exit(1);
        }
        else
        {
            szimb_tabla[*$2] = valtozo_leiro(d_loc__.first_line,Egesz,sorszam++);
            $$ = new utasitas_leiro( d_loc__.first_line, 
                szimb_tabla[*$2].cimke + " resb 4\n" );
        }
        delete $2;
    }
|
    LOGIKAI AZONOSITO
    {
        if( szimb_tabla.count(*$2) > 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$2 << "' valtozo mar definialva volt a "
            << szimb_tabla[*$2].def_sora << ". sorban." << std::endl;
            exit(1);
        }
        else
        {
            szimb_tabla[*$2] = valtozo_leiro(d_loc__.first_line,Logikai,sorszam++);
            $$ = new utasitas_leiro( d_loc__.first_line, 
                szimb_tabla[*$2].cimke + " resb 1\n" );
        }
        delete $2;
    }
|
    IDO AZONOSITO
    {
         if( szimb_tabla.count(*$2) > 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$2 << "' valtozo mar definialva volt a "
            << szimb_tabla[*$2].def_sora << ". sorban." << std::endl;
            exit(1);
        }
        else
        {
            szimb_tabla[*$2] = valtozo_leiro(d_loc__.first_line, Ido_t,sorszam++);
            $$ = new utasitas_leiro( d_loc__.first_line, 
                szimb_tabla[*$2].cimke + " resb 1\n" );
        }
        delete $2;       
    }
;

utasitasok:
    UTASITASOK utasitas utasitaslista
    {
        $$ = new utasitas_leiro( d_loc__.first_line,
            std::string("section .text\n") + "main:\n" + $2->kod + $3->kod );
        delete $2;
        delete $3;
    }
;

utasitaslista:
    // epsilon
    {
        $$ = new utasitas_leiro( d_loc__.first_line, "" );
    }
|
    utasitas utasitaslista
    {
        $$ = new utasitas_leiro( $1->sor, $1->kod + $2->kod );
        delete $1;
        delete $2;
    }
;

utasitas:
    SKIP
    {
        $$ = new utasitas_leiro( d_loc__.first_line, "" );
    }
|
    ertekadas
|
    be
|
    ki
|
    elagazas
|
    ciklus
;

ertekadas:
    AZONOSITO ERTEKADAS kifejezes
    {
        if( szimb_tabla.count( *$1 ) == 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$1 << "' valtozo nincs deklaralva." << std::endl;
            exit(1);
        }
        else if( szimb_tabla[*$1].vtip != $3->ktip )
        {
            std::cerr << d_loc__.first_line << ": Az ertekadas jobb- es baloldalan kulonbozo tipusu kifejezesek allnak." << std::endl;
            exit(1);
        }
        else
        {
            std::string reg;
            if( $3->ktip == Egesz )
                reg = "eax";
            else if ( $3->ktip == Logikai)
                reg = "al";
            else
                reg = "";
            $$ = new utasitas_leiro( d_loc__.first_line,
                $3->kod + "mov " + "[" + szimb_tabla[*$1].cimke + "],"  + reg + "\n" );
        }
        delete $3;
    }
;

be:
    BE AZONOSITO
    {
        if( szimb_tabla.count( *$2 ) == 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$2 << "' valtozo nincs deklaralva." << std::endl;
            exit(1);
        }
        else
        {
            std::string muvelet, reg;
            if( szimb_tabla[*$2].vtip == Egesz )
            {
                muvelet = "be_egesz";
                reg = "eax";
            }
            else
            {
                muvelet = "be_logikai";
                reg = "al";
            }
            $$ = new utasitas_leiro( d_loc__.first_line,
                "call " + muvelet + "\n" + "mov [" + szimb_tabla[*$2].cimke + "]," + reg + "\n" );
        }
        delete $2;
    }
;

ki:
    KI kifejezes
    {
        std::string muvelet;
        if( $2->ktip == Egesz )
            muvelet = "ki_egesz";
        else
            muvelet = "ki_logikai";
        $$ = new utasitas_leiro( d_loc__.first_line, $2->kod + "push eax\n" + "call " + muvelet + "\n" + "pop eax\n" );
        delete $2;
    }
;

elagazas:
    HA kifejezes AKKOR utasitaslista HA_VEGE
    {
        if( $2->ktip != Logikai )
        {
            std::cerr << d_loc__.first_line << ": Nem logikai tipusu az elagazas feltetele." << std::endl;
            exit(1);
        }
        else
        {
            std::stringstream out1;
            out1 << "Cimke" << Parser::sorszam++;
            std::string then = out1.str();
            std::stringstream out2;
            out2 << "Cimke" << Parser::sorszam++;
            std::string end = out2.str();
            $$ = new utasitas_leiro( $2->sor, 
                $2->kod + "cmp al,1\n" + "je " + then + "\n" + "jmp " + end + "\n"
                + then + ":\n" + $4->kod + end + ":\n" );
        }
        delete $2;
        delete $4;
    }
|
    HA kifejezes AKKOR utasitaslista KULONBEN utasitaslista HA_VEGE
    {
        if( $2->ktip != Logikai )
        {
            std::cerr << d_loc__.first_line << ": Nem logikai tipusu az elagazas feltetele." << std::endl;
            exit(1);
        }
        else
        {
            std::stringstream out1;
            out1 << "Cimke" << Parser::sorszam++;
            std::string then = out1.str();
            std::stringstream out2;
            out2 << "Cimke" << Parser::sorszam++;
            std::string elsec = out2.str();
            std::stringstream out3;
            out3 << "Cimke" << Parser::sorszam++;
            std::string end = out3.str();
            $$ = new utasitas_leiro( $2->sor, 
                $2->kod + "cmp al,1\n" + "je " + then + "\n" + "jmp " + elsec + "\n"
                + then + ":\n" + $4->kod + "jmp " + end + "\n" + elsec + ":\n"
                + $6->kod + end + ":\n" );
        }
        delete $2;
        delete $4;
        delete $6;
    }
;

ciklus:
    CIKLUS AMIG kifejezes utasitaslista CIKLUS_VEGE
    {
        if( $3->ktip != Logikai )
        {
            std::cerr << d_loc__.first_line << ": Nem logikai tipusu a ciklus feltetele." << std::endl;
            exit(1);
        }
        else
        {
            std::stringstream out1;
            out1 << "Cimke" << Parser::sorszam++;
            std::string eleje = out1.str();
            std::stringstream out2;
            out2 << "Cimke" << Parser::sorszam++;
            std::string mag = out2.str();
            std::stringstream out3;
            out3 << "Cimke" << Parser::sorszam++;
            std::string end = out3.str();
            $$ = new utasitas_leiro( $3->sor, eleje + ":\n"
                + $3->kod + "cmp al,1\n" + "je " + mag + "\n" + "jmp " + end + "\n"
                + mag + ":\n" + $4->kod + "jmp " + eleje + "\n" + end + ":\n" );
        }
        delete $3;
        delete $4;
    }
;

kifejezes:
    SZAMKONSTANS
    {
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, "mov eax," + *$1 + "\n");
        delete $1;
    }
|
    IGAZ
    {
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai, "mov al,1\n" );
    }
|
    HAMIS
    {
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai, "mov al,0\n" );
    }
|
    IDOKONST
    {
        $$ = new kifejezes_leiro( d_loc__.first_line, Ido_t, "mov al,0\n" );
    }
|
    AZONOSITO
    {
        if( szimb_tabla.count( *$1 ) == 0 )
        {
            std::cerr << d_loc__.first_line << ": A(z) '" << *$1 << "' valtozo nincs deklaralva." << std::endl;
            exit(1);
        }
        else
        {
            valtozo_leiro vl = szimb_tabla[*$1];
            std::string reg;
            if( vl.vtip == Egesz )
                reg = "eax";
            else
                reg = "al";

            $$ = new kifejezes_leiro( vl.def_sora, vl.vtip, "mov " + reg + ",[" + vl.cimke + "]\n" );
            delete $1;
        }
    }
|
    ORA BALZAROJEL kifejezes JOBBZAROJEL
    {
        if( $3->ktip != Ido_t)
        {
            std::cerr << $3->sor << ": Az ora függvény nem ido tipus-al lett meghivva." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, "");

        delete $3;
    }
|
    PERC BALZAROJEL kifejezes JOBBZAROJEL
    {
        if( $3->ktip != Ido_t)
        {
            std::cerr << $3->sor << ": A perc függvény nem ido tipus-al lett meghivva." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, "");  
        delete $3;
    }
|
    kifejezes PLUSZ kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '+' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '+' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "add eax,ebx\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes MINUSZ kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '-' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '-' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "sub eax,ebx\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes SZORZAS kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '*' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '*' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "mov edx,0\n" + "mul ebx\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes OSZTAS kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '/' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '/' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "mov edx,0\n" + "div ebx\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes MARADEK kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '%' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '%' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Egesz, $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "mov edx,0\n" + "div ebx\n" + "mov eax,edx\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes KISEBB kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '<' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '<' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        std::stringstream out;
        out << "Cimke" << Parser::sorszam++;
        std::string cimke = out.str();
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $3->kod + "push eax\n" + $1->kod + "pop ebx\n"
            + "cmp eax,ebx\n" + "mov al,1\n" + "jb " + cimke + "\n"
            + "mov al,0\n" + cimke + ":\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes NAGYOBB kifejezes
    {
        if( $1->ktip != Egesz )
        {
            std::cerr << $1->sor << ": A '>' operator baloldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Egesz )
        {
            std::cerr << $3->sor << ": A '>' operator jobboldalan nem egesz tipusu kifejezes all." << std::endl;
            exit(1);
        }
        std::stringstream out;
        out << "Cimke" << Parser::sorszam++;
        std::string cimke = out.str();
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $3->kod + "push eax\n" + $1->kod + "pop ebx\n"
            + "cmp eax,ebx\n" + "mov al,1\n" + "ja " + cimke + "\n"
            + "mov al,0\n" + cimke + ":\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes EGYENLO kifejezes
    {
        if( $1->ktip != $3->ktip )
        {
            std::cerr << $1->sor << ": Az '=' operator jobb- es baloldalan kulonbozo tipusu kifejezesek allnak." << std::endl;
            exit(1);
        }
        std::stringstream out;
        out << "Cimke" << Parser::sorszam++;
        std::string cimke = out.str();
        std::string reg1,reg2;
        if( $1->ktip == Egesz )
        {
            reg1 = "eax";
            reg2 = "ebx";
        }
        else
        {
            reg1 = "al";
            reg2 = "bl";
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $3->kod + "push eax\n" + $1->kod + "pop ebx\n"
            + "cmp " + reg1 + "," + reg2 + "\n" + "mov al,1\n" + "je " + cimke + "\n"
            + "mov al,0\n" + cimke + ":\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes ES kifejezes
    {
        if( $1->ktip != Logikai )
        {
            std::cerr << $1->sor << ": Az 'ES' operator baloldalan nem logikai tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Logikai )
        {
            std::cerr << $3->sor << ": Az 'ES' operator jobboldalan nem logikai tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "and al,bl\n" );
        delete $1;
        delete $3;
    }
|
    kifejezes VAGY kifejezes
    {
        if( $1->ktip != Logikai )
        {
            std::cerr << $1->sor << ": A 'VAGY' operator baloldalan nem logikai tipusu kifejezes all." << std::endl;
            exit(1);
        }
        if( $3->ktip != Logikai )
        {
            std::cerr << $3->sor << ": A 'VAGY' operator jobboldalan nem logikai tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $3->kod + "push eax\n" + $1->kod + "pop ebx\n" + "or al,bl\n" );
        delete $1;
        delete $3;
    }
|
    NEM kifejezes
    {
        if( $2->ktip != Logikai )
        {
            std::cerr << $2->sor << ": A 'NEM' operator utan nem logikai tipusu kifejezes all." << std::endl;
            exit(1);
        }
        $$ = new kifejezes_leiro( d_loc__.first_line, Logikai,
            $2->kod + "xor al,1\n" );
        delete $2;
    }
|
    BALZAROJEL kifejezes JOBBZAROJEL
    {
        $$ = $2;
    }
;
