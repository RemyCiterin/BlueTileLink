export PLRU;
export choose;
export next;
export Tree(..);
export toTree;
export fromTree;

typedef Bit#(TSub#(mshr,1)) PLRU#(numeric type mshr);

typedef union tagged {
  void Leaf;
  struct {
    Bit#(1) dir;
    Tree lhs;
    Tree rhs;
  } Node;
} Tree deriving(FShow, Eq);

function Tree toTree(PLRU#(mshr) plru);
  function Tree doRec(Integer pos, Integer size);
    if (size == 1) return Leaf;
    else begin
      Bit#(1) dir = plru[pos];

      Integer half = size / 2;
      Tree lhs = doRec(pos+1, half);
      Tree rhs = doRec(pos+half, size-half);

      return tagged Node {dir: dir, lhs: lhs, rhs: rhs};
    end
  endfunction


  return doRec(0, valueOf(mshr));
endfunction

function PLRU#(mshr) fromTree(Tree tree);
  function PLRU#(mshr) doRec(Tree t, Integer size);
    Integer half = size / 2;

    case (t) matches
      Leaf : return 0;
      tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin

        PLRU#(mshr) l = doRec(lhs, half) << 1;
        PLRU#(mshr) r = doRec(rhs, half) << half;

        return (dir == 1 ? 1 : 0) | l | r;
      end
    endcase
  endfunction

  return doRec(tree, valueOf(mshr));
endfunction

function Bit#(a) chooseTree(Tree tree, Integer size);
  Integer half = size / 2;

  case (tree) matches
    Leaf : return 0;
    tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin
      return dir == 1 ?
        1 + (chooseTree(lhs, half) << 1) :
        (chooseTree(rhs, half) << 1);
    end
  endcase
endfunction

function Bit#(TLog#(mshr)) choose(PLRU#(mshr) plru);
  return chooseTree(toTree(plru), valueOf(mshr));
endfunction

function Tree nextTree(Tree tree, Bit#(a) path, Integer size);
    Integer half = size / 2;

    case (tree) matches
      Leaf : return Leaf;
      tagged Node{dir: .dir, lhs: .lhs, rhs: .rhs} : begin
        return tagged Node{
          dir: ~path[0],
          lhs: path[0] == 1 ? nextTree(lhs, path >> 1, half) : lhs,
          rhs: path[0] == 0 ? nextTree(rhs, path >> 1, half) : rhs
        };
      end
    endcase
endfunction

function PLRU#(mshr) next(PLRU#(mshr) plru, Bit#(TLog#(mshr)) path);
  return fromTree(nextTree(toTree(plru), path, valueOf(mshr)));
endfunction
