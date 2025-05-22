import TLUtils :: *;
import Fifo :: *;
import Ehr :: *;

import RegFile :: *;
import RegFileUtils :: *;

export FreeList(..);
export mkFreeList;

export LinkedList(..);
export mkLinkedList;

// Return a free-list based allocator
interface FreeList#(numeric type indexW);
  // alloc a new unallocated index
  method ActionValue#(Bit#(indexW)) alloc;

  // free an index
  method Action free(Bit#(indexW) index);

  // return the number of not allocated entries
  method Bit#(TAdd#(indexW,1)) entries;
endinterface

module mkFreeList(FreeList#(indexW)) provisos (Alias#(Bit#(indexW), indexT));
  function Maybe#(indexT) genFreeList(indexT index);
    return index + 1 == 0 ? Invalid : Valid(index+1);
  endfunction

  Reg#(Maybe#(indexT)) free_head <- mkReg(Valid(0));

  RegFile#(indexT, Maybe#(indexT)) free_list <- mkRegFileFullGen(genFreeList);

  Reg#(Bit#(TAdd#(indexW,1))) counter <- mkReg(fromInteger(valueOf(TExp#(indexW))));

  method ActionValue#(indexT) alloc if (free_head matches tagged Valid .idx);
    actionvalue
      counter <= counter - 1;
      free_head <= free_list.sub(idx);
      free_list.upd(idx, Invalid);
      return idx;
    endactionvalue
  endmethod

  method entries = counter;

  method Action free(indexT index);
    action
      counter <= counter + 1;
      free_list.upd(index, free_head);
      free_head <= Valid(index);
    endaction
  endmethod
endmodule


// Define a type a simply linked list
// As example they are used in caches to store all the requests associated with
// a Miss Status Handling Register
interface LinkedList#(numeric type indexW);
  // create a new empty link list
  method ActionValue#(Bit#(indexW)) init;

  // return if their is still some place available
  method Bit#(TAdd#(indexW,1)) entries;

  // add an element to the head of the list and return the new head
  method ActionValue#(Bit#(indexW)) pushHead(Bit#(indexW) head);

  // add an element to the tail of the list and return the new tail
  method ActionValue#(Bit#(indexW)) pushTail(Bit#(indexW) tail);

  // remove the first element of the list
  method Action popHead(Bit#(indexW) head);

  // Join two lined lists
  method Action concat(Bit#(indexW) tail, Bit#(indexW) head);

  // return the next element in a linked list
  method Maybe#(Bit#(indexW)) next(Bit#(indexW) index);
endinterface

module mkLinkedList(LinkedList#(indexW)) provisos (Alias#(Bit#(indexW), indexT));
  RegFile#(indexT, Maybe#(indexT)) link <- mkRegFileFullInit(Invalid);

  FreeList#(indexW) free_list <- mkFreeList;

  function Action addLink(indexT from, indexT to);
      return link.upd(from, Valid(to));
  endfunction

  function Action deleteLink(indexT from);
    return link.upd(from, Invalid);
  endfunction

  method entries = free_list.entries;

  method ActionValue#(indexT) init;
    actionvalue
      let index <- free_list.alloc();
      return index;
    endactionvalue
  endmethod

  method ActionValue#(Bit#(indexW)) pushHead(Bit#(indexW) head);
    actionvalue
      let index <- free_list.alloc();
      addLink(index, head);
      return index;
    endactionvalue
  endmethod

  method ActionValue#(Bit#(indexW)) pushTail(Bit#(indexW) tail);
    actionvalue
      let index <- free_list.alloc();
      addLink(tail, index);
      return index;
    endactionvalue
  endmethod

  method Action popHead(Bit#(indexW) head);
    action
      free_list.free(head);
      deleteLink(head);
    endaction
  endmethod

  method Action concat(Bit#(indexW) tail, Bit#(indexW) head);
    action
      addLink(tail, head);
    endaction
  endmethod

  method Maybe#(Bit#(indexW)) next(Bit#(indexW) index);
    return link.sub(index);
  endmethod
endmodule

