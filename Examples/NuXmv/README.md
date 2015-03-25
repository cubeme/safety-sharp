## Fault Tree Analysis with COMPASS-Toolkit or FAME-Toolkit

```
NuSMV4Fame-linux64 -int -sa_compass -sa_ft_layering -sa_compass_task ffb.fail_obs_alm
> read_model -i ffb.smv
> go
> compute_fault_tree -t "Hazard"
```