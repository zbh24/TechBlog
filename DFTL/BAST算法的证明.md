# BAST算法的证明

标签（空格分隔）： 未分类

---

##BAST算法的思想
其它，都很像，唯一不同的是它会写到log块儿。
有两个表，一个日志块儿表，一个是log表。
- block mapping table
lbn pbn
- log表
lbn pbn lsns
1    20   {4,4,6,7}
这就是BAST算法，增加了一组log块儿，而且这些log块儿是组相联的，也就是这个log块儿都对应于某个数据块儿块儿。
可以认为data block是block-level，而log是sector-level的。
通常这些映射表是放在SRAM里面。

Merge:有这几种，
1）switch：直接交换
2）合并，merge

##BAST证明的架构
一共19个文件。
一些没有用的文件：
Params.v:参数设置，大小，长度
Data.v：char类型，空字符，满字符
上面都是一些参数设置和数据表示
Moand.v：定义一些操作，模拟命令的，主要有do return check
ListEx.v:列表上的操作，以及关于列表操作的证明
LibEx.v:其实也是类似操作，基本上用不到
bnat.v：关于nat的操作，blt，bgt函数
这六个文件没有什么重要的作用。

Nand：定义page，block，chip。然后定义操作，init_page,init_block.
read,write,erase.
NandLems：定义一些
nand_erase_block_spec:擦除以后新的怎么样，不影响旧的那些块儿
chip_set_block_elim:类似
nand_write_page_spec:类似

BAST:定义FTL层算法：
bmt：lbn->pbn
pmt:lbn->log
bit:block info table
fbq:free block queue
然后就是具体的操作，读日志块，读数据块儿，分配块儿，合并块儿。
再接着就是，FTL的操作，FTL_read,bmt_update_log,FTL_write

FTLProp:定义了一些pmt表的相关性质，也就是约束。
然后呢，block_coherent_log,block_coherent_data,block_coherent_erased这些很重要,这些都是定义bmt表里面的data和log和Nand的信息保持一致。
Inv:对FTL层的一些数据结构，如bit做出约束。如要么在bmt里面，要么在fbq里面。
每一个bmt里的pbn都是不同的，这都是定义的，我们定义出这些约束来，不然没办法证明。chip_bi_coherent，J_bi_block_coherent。然后就定义了终极的约束，F_INV,R_INV,Inv
InvLems:很多进展+保持的，就是证明一个东西进展以后还保持这个性质。
FTLLems:一些常用的说明(1)，还有一些read和write的spec(2)，ftl_write_spec,ftl_read_spec(3),Inv nand_init ftl_init等等(4)

Framework：
1)开始定义了一个hdd，然后hdd_write,hdd_read，hdd_init,command(cmd_read,cmd_write),behavior(bh_void,bh_value),hdd_run.hdd_run_cmd_list，然后hdd_write_atthesameaddr,hdd_write_notatthesameaddr.
2)然后是我们的flash，ftl_write,ftl_read,ftl_init,ftl_run。
3)然后有一个R。
Definition R (hdd: hard_disk) (fld: flash_device) : Prop :=
  forall sec, 
    hdd_read hdd sec = fld_read fld sec.

Verifivation：
证明:
R hdd_init fld_init.
fld_write_R_preservation:写过以后，仍然保持这个R关系。
fld_run_deterministic：（证明fld的唯一性）
一步进展，一步保持性质
多步进展，多步保持性质
最后一个正确性:
```
Theorem Correctness : 
  forall cl : list command, 
    forall (hd hd': hard_disk) (B: behavior) (fl: flash_device),
      hdd_run_cmd_list hdd_init cl hd' B
      -> exists fl': flash_device, fld_run_cmd_list fld_init cl fl' B.
```

-------------------------------------------------------------
辅助材料：
```
Inductive pmt_entry : Set :=
  | pmte_empty
  | pmte_log (off: page_off).

Definition page_mapping_table := list pmt_entry.

Inductive ftl_block_state : Set :=
  | bs_invalid
  | bs_erased
  | bs_data (lbn: block_no)
  | bs_log (lbn: block_no) (pmt: page_mapping_table).
 
(* 
BFTL adopts a block-level mapping table and transfer,a logical block number into two phyiscal block numbers. One of those is a phyiscal block for data, the other is for logging. Each entry in the table is a pair of physical block numbers. 

Two operations are provided for the block mapping table, bmt_get and bmt_update.
Both of them return either a value or none.
*)
(* bmt表里，一个lbn对应一个pbn和一个日志块号。 *)

Definition bmt_record := prod (option block_no) (option block_no).

Definition block_mapping_table := list bmt_record.

Definition bmt_get (bmt: block_mapping_table) (lbn: block_no) : option bmt_record :=
  list_get bmt lbn.
  
  
Inductive ftl_block_state : Set :=
  | bs_invalid
  | bs_erased
  | bs_data (lbn: block_no)
  | bs_log (lbn: block_no) (pmt: page_mapping_table).
  
Record block_info : Set := 
  mk_bi {
      bi_state: ftl_block_state;
      bi_used_pages: nat;
      bi_erase_count: nat
    }.

// 定义在Nand.v里面
Definition block_get_page (b: block) (off: page_off) : option page :=
  test (bvalid_page_off off);
  do p <-- (list_get (block_pages b) off);
  ret p.

Definition chip_bi_coherent (c: chip) (pbn: block_no) (bi: block_info) : Prop :=
  exists b, chip_get_block c pbn = Some b 
            /\ match (bi_state bi) with
                 | bs_erased => block_coherent_erased bi b
                 | bs_invalid => block_state b = bs_programmed
                 | bs_data _ => block_coherent_data bi b
                 | bs_log _ _ => block_coherent_log bi b
               end.

Definition J_bi_block_coherent (c: chip) (bit: block_info_table) := 
  forall pbn bi, 
    bit_get bit pbn = Some bi
    -> chip_bi_coherent c pbn bi.

  
// Inv
Definition F_Inv (f: FTL) : Prop :=
  let bit := ftl_bi_table f in
  let bmt := ftl_bm_table f in
  let fbq := ftl_free_blocks f in
    I_pbn_bit_valid bit         (* I1 *)
    /\ I_pbn_bmt_valid bmt      (* I2 *)
    /\ I_pbn_fbq_valid fbq   (* I3 *)
    /\ I_pbn_fbq_state bit fbq   (* I4 *)
    /\ I_pbn_bmt_used bit bmt       (* I5 *)
    /\ I_pbn_habitation bmt fbq     (* I6 *)
    /\ I_pbn_bmt_distinguishable bmt   (* I7_1 *)
    /\ I_pbn_bmt_distinguishable_2 bmt (* I7_2 *)
    /\ I_pbn_fbq_distinguishable fbq   (* I8 *)
    (* /\ I_blocks_abundant fbq            (* I9 *) *)
    /\ I_valid_lbn_has_entry_in_bmt bmt  (* I10 *).
    (* /\ I_used_blocks_less_than_2_max_lbn bit  (* I11 *). *)

Definition R_Inv (c: chip) (f: FTL) : Prop :=
  let bit := ftl_bi_table f in
  let bmt := ftl_bm_table f in
  let fbq := ftl_free_blocks f in
  J_bi_block_coherent c bit.

Definition Inv (c: chip) (f: FTL) := 
  F_Inv f /\ R_Inv c f.

//Framwwork.v

Definition flash_device := prod chip FTL.

```



