
Program PL0(input, output);
{ PL/0 compiler with code generation }

{常量定义}

Const 
  norw = 13;          {保留字的数目}
  txmax = 100;        {符号表长度}
  nmax = 14;          {数字的最大长度}
  al = 10;            {标识符的最大长度}
  amax = 2047;        {相对地址最大值}
  levmax = 3;         {最大嵌套层数}
  cxmax = 200;        {生成目标代码数组最大长度}

{类型变量定义}

Type symbol = ( nul,ident,number,plus,minus,times,slash,oddsym,eql,neq,lss,
               leq,gtr,geq,lparen,rparen,comma,semicolon,period,becomes,
               beginsym,endsym,ifsym,thensym,whilesym,dosym,callsym,constsym,
               varsym,procsym,readsym,writesym );
  {symbol的宏定义为一个枚举}
  alfa = packed array[1..al] Of char;
  {alfa宏定义为含有a1个元素的合并数组，为标识符的类型}
  objecttyp = (constant,variable,prosedure);
  {objecttyp的宏定义为一个枚举}
  symset = set Of symbol;    {symset为symbol的集合}
  fct = ( lit,opr,lod,sto,cal,int,jmp,jpc,red,wrt ); { functions }
  instruction = packed Record    {instruction声明为一个记录类型}
    f : fct;            {功能码}
    l : 0..levmax;      {嵌套层次}
    a : 0..amax;        {相对地址}
  End;


{LIT 0,a : 取常数a
  OPR 0,a : 执行运算a
  LOD l,a : 取层差为l的层﹑相对地址为a的变量
  STO l,a : 存到层差为l的层﹑相对地址为a的变量
  CAL l,a : 调用层差为l的过程
  INT 0,a : t寄存器增加a
  JMP 0,a : 转移到指令地址a处
  JPC 0,a : 条件转移到指令地址a处 }

{全局变量定义}

Var 
  ch : char;      {最后读出的字符}
  sym: symbol;    {最近识别出来符号类型}
  id : alfa;      {最后读出来的识别符}
  num: integer;   {最后读出来的数字}
  cc : integer;   {行缓冲区指针}
  ll : integer;   {行缓冲区长度}
  kk,err: integer;
  cx : integer;   {代码数组的当前下标}
  line: array[1..81] Of char;
  a : alfa;
  code : array[0..cxmax] Of instruction;
  word : array[1..norw] Of alfa;
  wsym : array[1..norw] Of symbol;
  ssym : array[char] Of symbol;
  mnemonic : array[fct] Of packed array[1..5] Of char;
  declbegsys, statbegsys, facbegsys : symset;
  table : array[0..txmax] Of
          Record
            name : alfa;
            Case kind: objecttyp Of 
              constant : (val:integer );
              variable,prosedure: (level,adr: integer )
          End;
  fin : text;       {源代码文件}
  finName: string;  {源程序文件名}
  fout : text;      {输出文件}
  foutName: string; {输出文件名}

Procedure error( n : integer );  {错误处理程序}
Begin
  writeln(fout, '****', ' ':cc-1, '^', n:2 );
  {报错提示信息，'^'指向出错位置，并提示错误类型}
  err := err + 1
End; { error }

Procedure getsym;    {词法分析程序}

Var i,j,k : integer;
Procedure getch;
Begin
  If cc = ll Then
    Begin
      If eof(fin) Then
        Begin
          writeln(fout,'program incomplete');
          close(fin);
          close(fout);
          exit;
        End;
      ll := 0;
      cc := 0;
      write(fout, cx:4,' ');  // source code
      While Not eoln(fin) Do
        Begin
          ll := ll + 1;
          Read(fin,ch);
          write(fout, ch);  // source code
          line[ll] := ch
        End;
      writeln(fout);  // source code
      readln(fin);
      ll := ll + 1;
      line[ll] := ' '
    End;
  cc := cc + 1;
  ch := line[cc]
End; { getch }
Begin {getsym}
  While ch = ' ' Do
    getch;
  If ch In ['a'..'z'] Then
    Begin {标识符或保留字}
      k := 0;
      Repeat
        If k < al Then
          Begin
            k := k + 1;
            a[k] := ch
          End;
        getch
      Until Not( ch In ['a'..'z','0'..'9']);
      If k >= kk Then kk := k
      Else
        Repeat
          a[kk] := ' ';
          kk := kk-1
        Until kk = k;
      id := a;
      i := 1;
      j := norw;
      Repeat
        k := (i+j) Div 2;
        If id <= word[k] Then j := k-1;
        If id >= word[k] Then i := k+1
      Until i > j;
      If i-1 > j
        Then sym := wsym[k]
      Else sym := ident
    End
  Else If ch In ['0'..'9'] Then
         Begin {数字}
           k := 0;
           num := 0;
           sym := number;
           Repeat
             num := 10*num+(ord(ch)-ord('0'));
             k := k+1;
             getch
           Until Not( ch In ['0'..'9']);
           If k > nmax Then error(30)
         End
  Else If ch = ':' Then
         Begin
           getch;
           If ch = '=' Then
             Begin
               sym := becomes;
               getch
             End
           Else sym := nul
         End
  Else If ch = '<' Then
         Begin
           getch;
           If ch = '=' Then
             Begin
               sym := leq;
               getch
             End
           Else If ch = '>' Then
                  Begin
                    sym := neq;
                    getch
                  End
           Else sym := lss
         End
  Else If ch = '>' Then
         Begin
           getch;
           If ch = '=' Then
             Begin
               sym := geq;
               getch
             End
           Else sym := gtr
         End
  Else
    Begin
      sym := ssym[ch];
      getch
    End
End; { getsym }

Procedure gen( x: fct; y,z : integer );
Begin
  If cx > cxmax Then
    Begin
      writeln(fout,'program too long');
      close(fin);
      close(fout);
      exit
    End;
  With code[cx] Do
    Begin
      f := x;
      l := y;
      a := z
    End;
  cx := cx + 1
End; { gen }

Procedure test( s1,s2 :symset; n: integer );
Begin
  If Not ( sym In s1 ) Then
    Begin
      error(n);
      s1 := s1 + s2;
      While Not( sym In s1) Do
        getsym
    End
End; { test }

Procedure block( lev,tx : integer; fsys : symset );

Var 
  dx : integer;
  tx0: integer;
  cx0: integer;
Procedure enter( k : objecttyp );
Begin
  tx := tx + 1;
  With table[tx] Do
    Begin
      name := id;
      kind := k;
      Case k Of 
        constant :
                   Begin
                     If num > amax Then
                       Begin
                         error(30);
                         num := 0
                       End;
                     val := num
                   End;
        variable :
                   Begin
                     level := lev;
                     adr := dx;
                     dx := dx + 1
                   End;
        prosedure: level := lev;
      End
    End
End; { enter }

Function position ( id : alfa ): integer;

Var i : integer;
Begin {在标识符表中查标识符id}
  table[0].name := id;
  i := tx;
  While table[i].name <> id Do
    i := i - 1;
  position := i
End;  { position }

Procedure constdeclaration;
Begin
  If sym = ident Then
    Begin
      getsym;
      If sym In [eql,becomes] Then
        Begin
          If sym = becomes Then error(1);
          getsym;
          If sym = number Then
            Begin
              enter(constant);
              getsym
            End
          Else error(2)
        End
      Else error(3)
    End
  Else error(4)
End; { constdeclaration }

Procedure vardeclaration;
Begin
  If sym = ident Then
    Begin
      enter(variable);
      getsym
    End
  Else error(4)
End; { vardeclaration }

Procedure listcode;

Var i : integer;
Begin
  For i := cx0 To cx-1 Do
    With code[i] Do
      writeln(fout, i:4, mnemonic[f]:7, l:3, a:5) // Intermediate Code
End; { listcode }

Procedure statement( fsys : symset );

Var i,cx1,cx2: integer;
Procedure expression( fsys: symset);

Var addop : symbol;
Procedure term( fsys : symset);

Var mulop: symbol ;
Procedure factor( fsys : symset );

Var i : integer;
Begin
  test( facbegsys, fsys, 24 );
  While sym In facbegsys Do
    Begin
      If sym = ident Then
        Begin
          i := position(id);
          If i= 0 Then error(11)
          Else
            With table[i] Do
              Case kind Of 
                constant : gen(lit,0,val);
                variable : gen(lod,lev-level,adr);
                prosedure: error(21)
              End;
          getsym
        End
      Else If sym = number Then
             Begin
               If num > amax Then
                 Begin
                   error(30);
                   num := 0
                 End;
               gen(lit,0,num);
               getsym
             End
      Else If sym = lparen Then
             Begin
               getsym;
               expression([rparen]+fsys);
               If sym = rparen Then getsym
               Else error(22)
             End;
      test(fsys,[lparen],23)
    End
End; {factor}
Begin {term}
  factor( fsys+[times,slash]);
  While sym In [times,slash] Do
    Begin
      mulop := sym;
      getsym;
      factor( fsys+[times,slash] );
      If mulop = times Then gen(opr, 0, 4)
      Else gen(opr, 0, 5)
    End
End; {term}
Begin {expression}
  If sym In [plus, minus] Then
    Begin
      addop := sym;
      getsym;
      term( fsys+[plus,minus]);
      If addop = minus Then gen(opr, 0, 1)
    End
  Else term( fsys+[plus,minus]);
  While sym In [plus,minus] Do
    Begin
      addop := sym;
      getsym;
      term( fsys+[plus,minus] );
      If addop = plus Then gen(opr,0,2)
      Else gen(opr,0,3)
    End
End; { expression }

Procedure condition( fsys : symset );

Var relop : symbol;
Begin
  If sym = oddsym Then
    Begin
      getsym;
      expression(fsys);
      gen(opr,0,6)
    End
  Else
    Begin
      expression( [eql,neq,lss,gtr,leq,geq]+fsys);
      If Not( sym In [eql,neq,lss,leq,gtr,geq]) Then
        error(20)
      Else
        Begin
          relop := sym;
          getsym;
          expression(fsys);
          Case relop Of 
            eql : gen(opr, 0, 8);
            neq : gen(opr, 0, 9);
            lss : gen(opr, 0, 10);
            geq : gen(opr, 0, 11);
            gtr : gen(opr, 0, 12);
            leq : gen(opr, 0, 13);
          End
        End
    End
End; {condition}
Begin {statement}
  If sym = ident Then
    Begin
      i := position(id);
      If i = 0 Then error(11)
      Else If table[i].kind <> variable Then
             Begin
               error(12);
               i := 0
             End;
      getsym;
      If sym = becomes Then getsym
      Else error(13);
      expression(fsys);
      If i <> 0 Then
        With table[i] Do
          gen(sto,lev-level,adr)
    End
  Else If sym = callsym Then
         Begin
           getsym;
           If sym <> ident Then error(14)
           Else
             Begin
               i := position(id);
               If i = 0 Then error(11)
               Else
                 With table[i] Do
                   If kind = prosedure Then
                     gen(cal,lev-level,adr)
                   Else error(15);
               getsym
             End
         End
  Else If sym = ifsym Then
         Begin
           getsym;
           condition([thensym,dosym]+fsys);
           If sym = thensym Then getsym
           Else error(16);
           cx1 := cx;
           gen(jpc,0,0);
           statement(fsys);
           code[cx1].a := cx
         End
  Else If sym = beginsym Then
         Begin
           getsym;
           statement([semicolon,endsym]+fsys);
           While sym In ([semicolon]+statbegsys) Do
             Begin
               If sym = semicolon Then getsym
               Else error(10);
               statement([semicolon,endsym]+fsys)
             End;
           If sym = endsym Then getsym
           Else error(17)
         End
  Else If sym = whilesym Then
         Begin
           cx1 := cx;
           getsym;
           condition([dosym]+fsys);
           cx2 := cx;
           gen(jpc,0,0);
           If sym = dosym Then getsym
           Else error(18);
           statement(fsys);
           gen(jmp,0,cx1);
           code[cx2].a := cx
         End
  Else If sym = readsym Then
         Begin
           getsym;
           If sym = lparen Then
             Repeat
               getsym;
               If sym = ident Then
                 Begin
                   i := position(id);
                   If i = 0
                     Then error(11)
                   Else If table[i].kind <> variable Then
                          Begin
                            error(12);
                            i := 0
                          End
                   Else With table[i] Do
                          gen(red,lev-level,adr)
                 End
               Else error(4);
               getsym;
             Until sym <> comma
           Else error(40);
           If sym <> rparen Then error(22);
           getsym
         End
  Else If sym = writesym Then
         Begin
           getsym;
           If sym = lparen Then
             Begin
               Repeat
                 getsym;
                 expression([rparen,comma]+fsys);
                 gen(wrt,0,0);
               Until sym <> comma;
               If sym <> rparen Then error(22);
               getsym
             End
           Else error(40)
         End;
  test(fsys,[],19)
End; {statement}
Begin {block}
  dx := 3;
  tx0 := tx;
  table[tx].adr := cx;
  gen(jmp,0,0);
  If lev > levmax Then error(32);
  Repeat
    If sym = constsym Then
      Begin
        getsym;
        Repeat
          constdeclaration;
          While sym = comma Do
            Begin
              getsym;
              constdeclaration
            End;
          If sym = semicolon Then getsym
          Else error(5)
        Until sym <> ident
      End;
    If sym = varsym Then
      Begin
        getsym;
        Repeat
          vardeclaration;
          While sym = comma Do
            Begin
              getsym;
              vardeclaration
            End;
          If sym = semicolon Then getsym
          Else error(5)
        Until sym <> ident;
      End;
    While sym = procsym Do
      Begin
        getsym;
        If sym = ident Then
          Begin
            enter(prosedure);
            getsym
          End
        Else error(4);
        If sym = semicolon Then getsym
        Else error(5);
        block(lev+1,tx,[semicolon]+fsys);
        If sym = semicolon Then
          Begin
            getsym;
            test( statbegsys+[ident,procsym],fsys,6)
          End
        Else error(5)
      End;
    test( statbegsys+[ident],declbegsys,7)
  Until Not ( sym In declbegsys );
  code[table[tx0].adr].a := cx;
  With table[tx0] Do
    Begin
      adr := cx;{代码开始地址}
    End;
  cx0 := cx;
  gen(int,0,dx);
  statement( [semicolon,endsym]+fsys);
  gen(opr,0,0); {生成返回指令}
  test(fsys, [], 8);
  listcode;
End { block };

Procedure interpret;

Const stacksize = 500;

Var p,b,t: integer;
  {程序地址寄存器, 基地址寄存器,栈顶地址寄存器}
  i : instruction;
  s : array[1..stacksize] Of integer; {数据存储栈}
Function base( l : integer ): integer;

Var b1 : integer; {顺静态链求层差为l的层的基地址}
Begin
  b1 := b;
  While l > 0 Do
    Begin
      b1 := s[b1];
      l := l-1
    End;
  base := b1
End; {base}
Begin
  writeln(fout, 'START PL/0' ); // Stack Data
  t := 0;
  b := 1;
  p := 0;
  s[1] := 0;
  s[2] := 0;
  s[3] := 0;
  Repeat
    i := code[p];
    p := p+1;
    With i Do
      Case f Of 
        lit :
              Begin
                t := t+1;
                s[t] := a;
              End;
        opr : Case a Of { operator }
                0:
                   Begin { return }
                     t := b-1;
                     p := s[t+3];
                     b := s[t+2];
                   End;
                1: s[t] := -s[t];
                2:
                   Begin
                     t := t-1;
                     s[t] := s[t]+s[t+1]
                   End;
                3:
                   Begin
                     t := t-1;
                     s[t] := s[t]-s[t+1]
                   End;
                4:
                   Begin
                     t := t-1;
                     s[t] := s[t]*s[t+1]
                   End;
                5:
                   Begin
                     t := t-1;
                     s[t] := s[t]Div s[t+1]
                   End;
                6: s[t] := ord(odd(s[t]));
                8:
                   Begin
                     t := t-1;
                     s[t] := ord(s[t]=s[t+1])
                   End;
                9:
                   Begin
                     t := t-1;
                     s[t] := ord(s[t]<>s[t+1])
                   End;
                10:
                    Begin
                      t := t-1;
                      s[t] := ord(s[t]< s[t+1])
                    End;
                11:
                    Begin
                      t := t-1;
                      s[t] := ord(s[t] >= s[t+1])
                    End;
                12:
                    Begin
                      t := t-1;
                      s[t] := ord(s[t] > s[t+1])
                    End;
                13:
                    Begin
                      t := t-1;
                      s[t] := ord(s[t] <= s[t+1])
                    End;
              End;
        lod :
              Begin
                t := t+1;
                s[t] := s[base(l)+a]
              End;
        sto :
              Begin
                s[base(l)+a] := s[t];
                writeln(fout,s[t]); // Stack data
                t := t-1
              End;
        cal :
              Begin {generate new block mark}
                s[t+1] := base(l);
                s[t+2] := b;
                s[t+3] := p;
                b := t+1;
                p := a;
              End;
        int : t := t+a;
        jmp : p := a;
        jpc :
              Begin
                If s[t] = 0
                  Then p := a;
                t := t-1;
              End;
        red :
              Begin
                write('??:');
                readln(s[base(l)+a]);
              End;
        wrt :
              Begin
                writeln(fout,s[t]); // PL0 write
                t := t+1
              End
      End { with,case }
  Until p = 0;
  writeln(fout,'END PL/0'); // Stack data
End; { interpret }

Begin { 主程序 }
  write('please input source program file name : ');
  readln(finName);
  assign(fin,finName);
  reset(fin); {打开fin}
  write('please input result file name : ');
  readln(foutName);
  assign(fout,foutName);
  rewrite(fout); {打开fout}

  For ch := 'A' To ';' Do
    ssym[ch] := nul;
  word[1] := 'begin        ';
  word[2] := 'call         ';
  word[3] := 'const        ';
  word[4] := 'do           ';
  word[5] := 'end          ';
  word[6] := 'if           ';
  word[7] := 'odd          ';
  word[8] := 'procedure    ';
  word[9] := 'read         ';
  word[10] := 'then         ';
  word[11] := 'var          ';
  word[12] := 'while        ';
  word[13] := 'write        ';

  wsym[1] := beginsym;
  wsym[2] := callsym;
  wsym[3] := constsym;
  wsym[4] := dosym;
  wsym[5] := endsym;
  wsym[6] := ifsym;
  wsym[7] := oddsym;
  wsym[8] := procsym;
  wsym[9] := readsym;
  wsym[10] := thensym;
  wsym[11] := varsym;
  wsym[12] := whilesym;
  wsym[13] := writesym;

  ssym['+'] := plus;
  ssym['-'] := minus;
  ssym['*'] := times;
  ssym['/'] := slash;
  ssym['('] := lparen;
  ssym[')'] := rparen;
  ssym['='] := eql;
  ssym[','] := comma;
  ssym['.'] := period;
  ssym['<'] := lss;
  ssym['>'] := gtr;
  ssym[';'] := semicolon;

  mnemonic[lit] := 'LIT  ';
  mnemonic[opr] := 'OPR  ';
  mnemonic[lod] := 'LOD  ';
  mnemonic[sto] := 'STO  ';
  mnemonic[cal] := 'CAL  ';
  mnemonic[int] := 'INT  ';
  mnemonic[jmp] := 'JMP  ';
  mnemonic[jpc] := 'JPC  ';
  mnemonic[red] := 'RED  ';
  mnemonic[wrt] := 'WRT  ';

  declbegsys := [ constsym, varsym, procsym ];
  statbegsys := [ beginsym, callsym, ifsym, whilesym];
  facbegsys := [ ident, number, lparen ];
  err := 0;
  cc := 0;
  cx := 0;
  ll := 0;
  ch := ' ';
  kk := al;
  getsym;
  block( 0,0,[period]+declbegsys+statbegsys );
  If sym <> period
    Then error(9);
  If err = 0
    Then interpret
  Else write('ERRORS IN PL/0 PROGRAM');
  writeln(fout);
  close(fin);
  close(fout);
End.
