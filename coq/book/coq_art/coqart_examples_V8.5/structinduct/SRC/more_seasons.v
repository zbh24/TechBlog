Add LoadPath ".".
Require Export seasons.
Require Export month.

Definition month_season :=
 month_rec (fun _ => season)
           Winter Winter Winter
           Spring Spring Spring
           Summer Summer Summer
           Autumn Autumn Autumn.

Reset month_season.

Definition month_season (m:month) : season :=
  match m with
  | January => Winter
  | February => Winter
  | March => Winter
  | April => Spring
  | May => Spring
  | June => Spring
  | July => Summer
  | August => Summer
  | September => Summer
  | October => Autumn
  | November => Autumn
  | December => Autumn
  end.
