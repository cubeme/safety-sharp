## Fault Tree Analysis with COMPASS-Toolkit or FAME-Toolkit

```
$ NuSMV4Fame-linux64 -int -sa_compass -sa_ft_layering -sa_compass_task ffb.fail_obs_alm
> read_model -i ffb.smv
> go
to generate cut sets
> compute_fault_tree -t "Hazard"

to generate ordered cut sets
> compute_fault_tree -d "Hazard"

to check all properties in the file
> check_property
```