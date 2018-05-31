pragma solidity ^0.4.21;

/*
variables
  i     identifier
  u, v  user
  Δc    GEM
  Δd    CHI
  ΔX    DAI/CHI
  ΔD    DAI

storage
  c     identifier -> user -> GEM
  C     identifier -> user -> GEM
  d     identifier -> user -> CHI
  D     user -> DAI
  X     identifier -> DAI/CHI
  Y     identifier -> DAI/GEM
  q     identifier -> CHI
  Q     identifier -> CHI
  p, P  DAI
  V     DAI
  G     boolean

rage  ≡  G
rope  ≡  P  p
rave  ≡  V

cageᵣ  =  set  G=1
copeᵣ O  =  set  P=O
caveᵣ ΔV  =  V↑p↑ΔV

geld u  ≡  Dᵤ
gold i u  ≡  Cᵢᵤ
peek i u  ≡  cᵢᵤ  dᵢᵤ

look i  ≡  Xᵢ
feel i  ≡  Yᵢ
grip i  ≡  Qᵢ  qᵢ

foldᵣ i ΔX  =  set  Xᵢ↑ΔX  V↑p↑ΔX★qᵢ
moldᵣ i Y  =  set  Yᵢ=Y
holdᵣ i Q  =  set  Qᵢ=Q

frobᵤ i Δc Δd  =  iff  ¬G
 set  cᵢᵤ↑Cᵢᵤ↓Δc  dᵢᵤ↑qᵢ↑Δd  Dᵤ↑p↑Xᵢ★Δd
 iff  Xᵢ★dᵢᵤ ≤ Yᵢ★cᵢᵤ  or  Δd ≤ 0 ∧ Δc ≥ 0
 iff  Xᵢ★qᵢ ≤ Qᵢ ∧ p ≤ P  or  Δd ≤ 0

grabᵣ i u  =  set  cᵢᵤ=0  V↓p↓Xᵢ★dᵢᵤ  dᵢᵤ↓qᵢ↓dᵢᵤ

moveᵣ u v ΔD  =  Dᵤ↓Dᵥ↑ΔD
suckᵣ u ΔD  =  V↓Dᵤ↑ΔD

*/

contract Coinz {

    function add_overflows(int x, int y) internal pure returns (bool b) {
        return y > 0 && x+y <= x || y < 0 && x+y >= x;
    }

    /* post: reverted <=> add_overflows(x, y) */
    function add(int x, int y) internal pure returns (int z) {
        z = x + y;
        // revert iff overflow:
        require(y <= 0 || z > x);
        require(y >= 0 || z < x);
    }

    function sub(int x, int y) internal pure returns (int z) {
        // -y overflows if y is MIN_INT:
        require(y != -2**255);
        z = add(x, -y);
    }

    function mul(int x, int y) internal pure returns (int z) {
        z = x * y;
        // revert iff overflow:
        require(y >= 0 || x != -2**255);
        require(y == 0 || z / y == x);
    }

    struct Urn {
        int c; // GEM
        int C; // GEM
        int d; // CHI
    }

    struct Ilk {
        int X; // rate CHI/DAI
        int Y; // spot DAI/GEM (i.e. price in DAI per collateral unit)
        int q; // CHI loans issued
        int Q; // DAI loan cap
    }

    modifier auth {
        require(msg.sender == root);
        _;
    }

    modifier anyone {
        require(msg.sender == root || msg.sender != root);
        _;
    }

    bool public G;
    address root;
    int public p; // DAI supply
    int public P; // DAI cap
    int public V; // DAI vow
    mapping (address => int) public D;
    mapping (address => mapping (bytes32 => Urn)) public urns;
    mapping (bytes32 => Ilk) public ilks;
    constructor() public {
        root = msg.sender;
    }
    int ONE = 10**27;
    // all functions have:
    //    precondition: !G => invariant()
    //    postcondition: !G => invariant()
    // don't really know yet what happens with the invariant when G has happened
    function invariant() internal anyone returns (bool ok) {
        ok = true;
        ok = ok && p >= 0;
        ok = ok && P >= 0;
        ok = ok && V >= 0;
        uint256 i = 0;
        int S = 0;
        do {
            bytes32 name = bytes32(i);
            uint160 u = 0;
            address user;
            if (ilks[name].X != 0) {
                ok = ok && ilks[name].X > 0;
                ok = ok && ilks[name].Y >= 0;
                ok = ok && ilks[name].q >= 0;
                ok = ok && ilks[name].Q >= 0;
                int s = 0;
                do {
                    user = address(u);
                    ok = ok && D[user] >= 0;
                    ok = ok && urns[user][name].c >= 0;
                    ok = ok && urns[user][name].C >= 0;
                    ok = ok && urns[user][name].d >= 0;
                    s += urns[user][name].d;
                    S += D[user];
                } while (++u == 0);
                ok = ok && s == ilks[name].q;
            } else {
                ok = ok && ilks[name].Y == 0;
                ok = ok && ilks[name].q == 0;
                ok = ok && ilks[name].Q == 0;
                do {
                    user = address(u);
                    ok = ok && urns[user][name].c == 0;
                    ok = ok && urns[user][name].C == 0;
                    ok = ok && urns[user][name].d == 0;
                } while (++u == 0);
            }
        } while (++i == 0);
        ok = ok && p == S + V;
    }
    /*
        frobᵤ i Δc Δd  =  iff  ¬G
         set  cᵢᵤ↑Cᵢᵤ↓Δc  dᵢᵤ↑qᵢ↑Δd  Dᵤ↑p↑Xᵢ★Δd
         iff  Xᵢ★dᵢᵤ ≤ Yᵢ★cᵢᵤ  or  Δd ≤ 0 ∧ Δc ≥ 0
         iff  Xᵢ★qᵢ ≤ Qᵢ ∧ p ≤ P  or  Δd ≤ 0

        post:
            reverted <=>
                || G
                || ilk.X == 0
                || add_overflows(urn.c, dc)
                || sub_overflows(urn.C, dc)
                || add_overflows(urn.d, dd)
                || add_overflows(ilk.q, dd)
                || !(dd <= 0 && dd >= 0) && (mul_overflows(d, ilk.X))
                || !(dd <= 0 && dd >= 0) && (mul_overflows(c, ilk.Y))
                || !(dd <= 0) && (mul_overflows(urn.X, q))
                || mul_overflows(d, ilk.X)
                || add_overflows(D[msg.sender], ilk.X * dd)
                || add_overflows(p, ilk.X * dd)
                || !((dd <= 0 && dc >= 0) || (urn.d + dd) * ilk.X <= (urn.c + dc) * ilk.Y)
                || !(dd <= 0 || (ilk.X + q * dd) <= ilk.Q && p + ilk.X * dd <= P)
                || ! && urn.c + dc >= 0
                     && urn.C - dc >= 0
                     && urn.d + dd >= 0
                     && D[msg.sender] + ilk.X * dd >= 0

        postcondition "reclaimable":
          exist DD . dd = DD * X ==>
          won't revert due to multiplication overflow if (dd <= 0 && dc >= 0)
          (if it reverts here it is for some other reason)

        modifies urn, D[msg.sender], ilk.q, p

        post:
            ! reverted =>
                && urn'.c == urn.c + dc
                && urn'.C == urn.C - dc
                && urn'.d == urn.d + dd
                && D'[msg.sender] == D[msg.sender] + ilk.X * dd
                && ilk'.q == q + dd
                && p' == p + X * dd

    */
    function frob(bytes32 name, int dc, int dd) public anyone {
        require(!G);
        Urn storage urn = urns[msg.sender][name];
        Ilk storage ilk = ilks[name];
        require(ilks[name].X != 0);
        int c = add(urn.c, dc);
        int C = sub(urn.C, dc);
        int d = add(urn.d, dd);
        int q = add(ilk.q, dd);
        int _D = add(D[msg.sender], mul(ilk.X, dd));
        p = add(p, mul(ilk.X, dd));
        // these two || should be short-circuiting to make "reclaimable" work:
        require((dd <= 0 && dc >= 0) || mul(d, ilk.X) <= mul(c, ilk.Y));
        require(dd <= 0 || (mul(ilk.X, q) <= ilk.Q && p <= P));
        require(c >= 0 && C >= 0 && d >= 0 && _D >= 0);
        urn.c = c;
        urn.C = C;
        urn.d = d;
        D[msg.sender] = _D;
        ilk.q = q;
    }
    // initialize a new Ilk
    function init(bytes32 name) public auth {
        require(ilks[name].X == 0);
        ilks[name].X = ONE;
    }
    /*
        foldᵣ i ΔX  =  set  Xᵢ↑ΔX  V↑p↑ΔX★qᵢ

        post: reverted <=>
                || ilks[name].X == 0
                || ilks[name].X + dX <= 0
                || mul_overflows(dX, ilks[name].q)
                || add_overflows(V, dX * ilks[name].q)
                || add_overflows(p, dX * ilks[name].q)
        modifies V, p, ilks[name].X
        post: !reverted ==> ilks'[name].X == ilks[name].X + dX
        post: !reverted ==> V' == V + dX * ilks[name].q
        post: !reverted ==> p' == p + dX * ilks[name].q
    */
    function fold(bytes32 name, int dX) public auth {
        require(ilks[name].X != 0);
        ilks[name].X += dX;
        require(ilks[name].X > 0);
        V = add(V, mul(dX, ilks[name].q));
        p = add(p, mul(dX, ilks[name].q));
    }
    /*
        moldᵣ i Y  =  set  Yᵢ=Y

        modifies ilks[name].Y

        post: (reverted <=> ilks[name].X == 0 || Y < 0)
        post: !reverted ==> ilks'[name].Y == Y
    */
    function mold(bytes32 name, int Y) public auth {
        require(ilks[name].X != 0);
        require(Y >= 0);
        ilks[name].Y = Y;
    }
    /*
        holdᵣ i Q  =  set  Qᵢ=Q

        modifies ilks[name].Q

        post: (reverted <=> ilks[name].X == 0 || Q < 0)
        post: !reverted ==> ilks'[name].Q == Q
    */
    //Update the debt ceiling for this particular collateral type
    function hold(bytes32 name, int Q) public auth {
        require(ilks[name].X != 0);
        require(Q >= 0);
        ilks[name].Q = Q;
    }
    /*
        slipᵣ i u Δc  =  cᵢᵤ↑Δc

        modifies urns[user][name].C

        post: reverted <=>
                || ilks[name].X == 0
                || add_overflows(urns[user][name], dC)
                || urns[user][name].C + dC < 0
        post: !reverted ==> urns'[user][name].C == urns[user][name] + dC
    */
    function slip(address user, bytes32 name, int dC) public auth {
        int _C = add(urns[user][name].C, dC);
        require(_C >= 0);
        urns[user][name].C = _C;
    }
    /*
        grabᵣ i u  =  set  cᵢᵤ=0  V↓p↓Xᵢ★dᵢᵤ  dᵢᵤ↓qᵢ↓dᵢᵤ

        Where ↧ means: can become negative
    */
    function grab(bytes32 name, address owner) public auth {
        require(ilks[name].X != 0); // might not be strictly necessary
        urns[owner][name].c = 0;
        int w = mul(ilks[name].X, urns[owner][name].d);
        V = sub(V, w);
        p = sub(V, w);
        ilks[name].q = sub(ilks[name].q, urns[owner][name].d);
        urns[owner][name].d = 0;
    }
    /* caveᵣ ΔV  =  V↑p↑ΔV */
    function cave(int dV) public auth {
        require(!G);
        V = add(V, dV);
        p = add(p, dV);
        require(p >= 0); // ?
    }
    // modifies G
    // post: G = true
    function cage() public auth {
        G = true;
    }
    //Set total Dai cap to O
    function cope(int O) public auth {
        require(O >= 0);
        P = O;
    }
    // moveᵣ u v ΔD  =  Dᵤ↓Dᵥ↑ΔD
    function move(address user, address other, int dD) public auth {
        D[user] = sub(D[user], dD);
        D[other] = sub(D[other], dD);
        require(D[user] >= 0);
        require(D[other] >= 0);
    }
    // suckᵣ u ΔD  =  V↓Dᵤ↑ΔD
    function suck(address user, int dD) public auth {
        D[user] = add(D[user], dD);
        V = sub(V, dD);
        require(D[user] >= 0);
    }
}
