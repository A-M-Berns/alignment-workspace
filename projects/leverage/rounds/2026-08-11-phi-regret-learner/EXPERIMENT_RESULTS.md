# Experiment results

Evidence status: **numerical experiment**, except exact-rational distribution, decoding, and charge equalities are separately test-supported. Decimal precision is 80 digits; displayed values are rounded to nine decimal places. The sampled histories are integration witnesses, not pathwise regret evidence.

Comparator class: identity, repair_declines, repair_declines_even, repair_declines_odd, toll_declines_1, toll_declines_2, toll_declines_4, default_declines, withdraw_merits

| fixture | T | policy | mixed charge | max regret | max/T | max/scale | beta | source bound |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| persistent_interval | 12 | uniform | 9.000000000 | 3.000000000 | 0.250000000 | 0.103280521 | — | — |
| persistent_interval | 12 | hedge_actions | 3.438377934 | 0.702709126 | 0.058559094 | 0.024192055 | — | — |
| persistent_interval | 12 | blum_mansour | 6.000000000 | 0.000000000 | 0.000000000 | 0.000000000 | 0.298109029 | 153.945310718 |
| persistent_interval | 24 | uniform | 18.000000000 | 6.000000000 | 0.250000000 | 0.146060713 | — | — |
| persistent_interval | 24 | hedge_actions | 4.934902835 | 0.938197488 | 0.039091562 | 0.022838966 | — | — |
| persistent_interval | 24 | blum_mansour | 12.000000000 | 0.000000000 | 0.000000000 | 0.000000000 | 0.424939488 | 161.627042663 |
| persistent_interval | 48 | uniform | 36.000000000 | 12.000000000 | 0.250000000 | 0.206561041 | — | — |
| persistent_interval | 48 | hedge_actions | 6.972919424 | 1.271323724 | 0.026485911 | 0.021883829 | — | — |
| persistent_interval | 48 | blum_mansour | 24.000000000 | 0.000000000 | 0.000000000 | 0.000000000 | 0.545993616 | 186.227123150 |
| persistent_interval | 96 | uniform | 72.000000000 | 24.000000000 | 0.250000000 | 0.292121426 | — | — |
| persistent_interval | 96 | hedge_actions | 9.781569198 | 1.743439019 | 0.018160823 | 0.021220662 | — | — |
| persistent_interval | 96 | blum_mansour | 48.000000000 | 0.000000000 | 0.000000000 | 0.000000000 | 0.651873828 | 228.568527882 |
| impediment_pressure | 12 | uniform | 9.000000000 | 7.500000000 | 0.625000000 | 0.258201302 | — | — |
| impediment_pressure | 12 | hedge_actions | 3.438377934 | 2.736304474 | 0.228025373 | 0.094202317 | — | — |
| impediment_pressure | 12 | blum_mansour | 4.379029004 | 2.879029004 | 0.239919084 | 0.099115871 | 0.298109029 | 153.945310718 |
| impediment_pressure | 24 | uniform | 18.000000000 | 15.000000000 | 0.625000000 | 0.365151782 | — | — |
| impediment_pressure | 24 | hedge_actions | 4.934902835 | 3.928841722 | 0.163701738 | 0.095641571 | — | — |
| impediment_pressure | 24 | blum_mansour | 7.022685512 | 4.022685512 | 0.167611896 | 0.097926052 | 0.424939488 | 161.627042663 |
| impediment_pressure | 48 | uniform | 36.000000000 | 30.000000000 | 0.625000000 | 0.516402603 | — | — |
| impediment_pressure | 48 | hedge_actions | 6.972919424 | 5.561852775 | 0.115871933 | 0.095738508 | — | — |
| impediment_pressure | 48 | blum_mansour | 11.571913632 | 5.571913632 | 0.116081534 | 0.095911690 | 0.545993616 | 186.227123150 |
| impediment_pressure | 96 | uniform | 72.000000000 | 60.000000000 | 0.625000000 | 0.730303565 | — | — |
| impediment_pressure | 96 | hedge_actions | 9.781569198 | 7.809409275 | 0.081348013 | 0.095053991 | — | — |
| impediment_pressure | 96 | blum_mansour | 19.747920026 | 7.747920026 | 0.080707500 | 0.094305560 | 0.651873828 | 228.568527882 |
| fully_licensed | 12 | uniform | 9.000000000 | 7.500000000 | 0.625000000 | 0.258201302 | — | — |
| fully_licensed | 12 | hedge_actions | 3.438377934 | 2.736304474 | 0.228025373 | 0.094202317 | — | — |
| fully_licensed | 12 | blum_mansour | 5.633432048 | 3.008432048 | 0.250702671 | 0.103570809 | 0.298109029 | 153.945310718 |
| fully_licensed | 24 | uniform | 18.000000000 | 15.000000000 | 0.625000000 | 0.365151782 | — | — |
| fully_licensed | 24 | hedge_actions | 4.934902835 | 3.928841722 | 0.163701738 | 0.095641571 | — | — |
| fully_licensed | 24 | blum_mansour | 9.364493127 | 4.114493127 | 0.171437214 | 0.100160967 | 0.424939488 | 161.627042663 |
| fully_licensed | 48 | uniform | 36.000000000 | 30.000000000 | 0.625000000 | 0.516402603 | — | — |
| fully_licensed | 48 | hedge_actions | 6.972919424 | 5.561852775 | 0.115871933 | 0.095738508 | — | — |
| fully_licensed | 48 | blum_mansour | 16.153875722 | 5.653875722 | 0.117789078 | 0.097322538 | 0.545993616 | 186.227123150 |
| fully_licensed | 96 | uniform | 72.000000000 | 60.000000000 | 0.625000000 | 0.730303565 | — | — |
| fully_licensed | 96 | hedge_actions | 9.781569198 | 7.809409275 | 0.081348013 | 0.095053991 | — | — |
| fully_licensed | 96 | blum_mansour | 28.828499541 | 7.828499541 | 0.081546870 | 0.095286352 | 0.651873828 | 228.568527882 |

Blum--Mansour comparator detail:

| fixture | T | comparator | counterfactual charge | regret | positive-saving mass |
|---|---:|---|---:|---:|---:|
| persistent_interval | 12 | identity | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | repair_declines | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | repair_declines_even | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | repair_declines_odd | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | toll_declines_1 | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | toll_declines_2 | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | toll_declines_4 | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | default_declines | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 12 | withdraw_merits | 6.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | identity | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | repair_declines | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | repair_declines_even | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | repair_declines_odd | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | toll_declines_1 | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | toll_declines_2 | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | toll_declines_4 | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | default_declines | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 24 | withdraw_merits | 12.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | identity | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | repair_declines | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | repair_declines_even | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | repair_declines_odd | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | toll_declines_1 | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | toll_declines_2 | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | toll_declines_4 | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | default_declines | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 48 | withdraw_merits | 24.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | identity | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | repair_declines | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | repair_declines_even | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | repair_declines_odd | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | toll_declines_1 | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | toll_declines_2 | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | toll_declines_4 | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | default_declines | 48.000000000 | 0.000000000 | 0.000000000 |
| persistent_interval | 96 | withdraw_merits | 48.000000000 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | identity | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | repair_declines | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | repair_declines_even | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | repair_declines_odd | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | toll_declines_1 | 12.750000000 | -8.370970996 | 0.000000000 |
| impediment_pressure | 12 | toll_declines_2 | 9.000000000 | -4.620970996 | 1.009537797 |
| impediment_pressure | 12 | toll_declines_4 | 1.500000000 | 2.879029004 | 2.374260105 |
| impediment_pressure | 12 | default_declines | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 12 | withdraw_merits | 4.379029004 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | identity | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | repair_declines | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | repair_declines_even | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | repair_declines_odd | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | toll_declines_1 | 25.500000000 | -18.477314488 | 0.000000000 |
| impediment_pressure | 24 | toll_declines_2 | 18.000000000 | -10.977314488 | 1.395277530 |
| impediment_pressure | 24 | toll_declines_4 | 3.000000000 | 4.022685512 | 3.325046748 |
| impediment_pressure | 24 | default_declines | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 24 | withdraw_merits | 7.022685512 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | identity | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | repair_declines | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | repair_declines_even | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | repair_declines_odd | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | toll_declines_1 | 51.000000000 | -39.428086368 | 0.000000000 |
| impediment_pressure | 48 | toll_declines_2 | 36.000000000 | -24.428086368 | 1.926111725 |
| impediment_pressure | 48 | toll_declines_4 | 6.000000000 | 5.571913632 | 4.608857769 |
| impediment_pressure | 48 | default_declines | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 48 | withdraw_merits | 11.571913632 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | identity | 19.747920026 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | repair_declines | 19.747920026 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | repair_declines_even | 19.747920026 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | repair_declines_odd | 19.747920026 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | toll_declines_1 | 102.000000000 | -82.252079974 | 0.000000000 |
| impediment_pressure | 96 | toll_declines_2 | 72.000000000 | -52.252079974 | 2.674445286 |
| impediment_pressure | 96 | toll_declines_4 | 12.000000000 | 7.747920026 | 6.410697383 |
| impediment_pressure | 96 | default_declines | 19.747920026 | 0.000000000 | 0.000000000 |
| impediment_pressure | 96 | withdraw_merits | 19.747920026 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | identity | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | repair_declines | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | repair_declines_even | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | repair_declines_odd | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | toll_declines_1 | 16.687500000 | -11.054067952 | 0.000000000 |
| fully_licensed | 12 | toll_declines_2 | 12.000000000 | -6.366567952 | 1.050725613 |
| fully_licensed | 12 | toll_declines_4 | 2.625000000 | 3.008432048 | 2.483069241 |
| fully_licensed | 12 | default_declines | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 12 | withdraw_merits | 5.633432048 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | identity | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | repair_declines | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | repair_declines_even | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | repair_declines_odd | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | toll_declines_1 | 33.375000000 | -24.010506873 | 0.000000000 |
| fully_licensed | 24 | toll_declines_2 | 24.000000000 | -14.635506873 | 1.427584860 |
| fully_licensed | 24 | toll_declines_4 | 5.250000000 | 4.114493127 | 3.400700697 |
| fully_licensed | 24 | default_declines | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 24 | withdraw_merits | 9.364493127 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | identity | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | repair_declines | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | repair_declines_even | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | repair_declines_odd | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | toll_declines_1 | 66.750000000 | -50.596124278 | 0.000000000 |
| fully_licensed | 48 | toll_declines_2 | 48.000000000 | -31.846124278 | 1.956463518 |
| fully_licensed | 48 | toll_declines_4 | 10.500000000 | 5.653875722 | 4.675643963 |
| fully_licensed | 48 | default_declines | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 48 | withdraw_merits | 16.153875722 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | identity | 28.828499541 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | repair_declines | 28.828499541 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | repair_declines_even | 28.828499541 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | repair_declines_odd | 28.828499541 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | toll_declines_1 | 133.500000000 | -104.671500459 | 0.000000000 |
| fully_licensed | 96 | toll_declines_2 | 96.000000000 | -67.171500459 | 2.704435225 |
| fully_licensed | 96 | toll_declines_4 | 21.000000000 | 7.828499541 | 6.476281929 |
| fully_licensed | 96 | default_declines | 28.828499541 | 0.000000000 | 0.000000000 |
| fully_licensed | 96 | withdraw_merits | 28.828499541 | 0.000000000 | 0.000000000 |

Integration audit (sampled Blum--Mansour path at T=96):

| fixture | record | identity | canonical | no erasure | response service | non-capture | compute priced | integrated |
|---|---|---|---|---|---|---|---|---|
| persistent_interval | yes | yes | yes | yes | yes | yes | no | no |
| impediment_pressure | yes | yes | yes | yes | yes | yes | no | no |
| fully_licensed | yes | yes | yes | yes | yes | yes | no | no |
