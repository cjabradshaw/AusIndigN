# Net primary production models for Australia to estimate carrying capacity of pre-colonial Indigenous population
### (includes code to compare predictions to anthropological/historical accounts, and a demographic model to estimate the number of excess deaths occurring from pre-colonial period to late 19<sup>th</sup> Century)
<a href="https://www.ucy.ac.cy/migrate/"><img align="right" src="www/MigratelogoShad.png" width="200" style="margin-top: 20px"></a>
<a href="https://zenodo.org/doi/10.5281/zenodo.10561469"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.10561469.svg" alt="DOI"></a>

## Focal manuscript
Williams, AN, K Beller, MI Bird, B Griffiths, S Ingrey, IJ McNiven, MC Nitschke, N Pitt, L Russell, F Saltré, S Ulm, C Wilson, CJA Bradshaw. <a href="">Multi-model estimates of the size of the Australian Indigenous population prior to and its massive decline following colonial invasion</a>. In review

## Abstract
Estimating the size of pre-colonial Indigenous populations in Australia and the magnitude of impact of colonial invasion in 1788 is essential to inform the management of intergenerational trauma and reconciliation, and provide baseline information to apply contemporary socio-economic and environmental activities. Our understanding of these populations is poor due to the early exposure of lethal diseases, extensive frontier violence and killing, and a lack of any systematic censuses. Here we review ethnographic observations, archaeological and genetic reconstructions, and carrying capacity calculated from hindcasted climate models to estimate the abundance of the Indigenous population prior to colonial invasion, and the inferred number of excess deaths in post-colonial times. Congruency of the modelled population size suggests a bootstrapped median of 2.51 million people in the pre-colonial population (75% confidence interval: 1.13–4.41 million, or 0.33 people km<sup>-2</sup>; 75% confidence interval: 0.15–0.57 km<sup>-2</sup>) based on these studies, with more recent approaches reflecting higher values in this range. At a median pre-colonial population of 2.51 million, approximately 32,500 excess deaths year<sup>-1</sup> (approximately 2.39 million deaths in total) would have had to occur in the late 18<sup>th</sup> and early 19<sup>th</sup> Centuries from colonial invasion-related incidents on average to achieve the estimated population of 0.177–0.193 million by 1861 (i.e., 7–8% of the pre-colonial population). These findings highlight the major impact experienced by Indigenous people, and demonstrate a remarkable story of survival, resilience, and recovery over the last 235 years. However, even today, the Indigenous population remains at ~ 32% of its median pre-colonial size, and further efforts in their support must form a focus to achieve reconciliation into the future.

## <a href="https://github.com/cjabradshaw/AusIndigN/tree/main/scripts">Scripts</a>
R code by Corey Bradshaw (<a href="http://github.com/cjabradshaw">@cjabradshaw</a>)

### base script
- <code>indigN.R</code>: includes all code used to derive estimates reported in the paper mentioned above

### <a href="https://github.com/cjabradshaw/AusIndigN/tree/main/scripts/source">source functions</a>
- <code>matrixOperators.r</code>: functions for manipulating matrices for population projections
- <code>new_lmer_AIC_tables3.r</code>: functions to calculate information-theoretic parameters for linear models
- <code>r.squared.r</code>: functions to calculate goodness of fit for linear models

## <a href="https://github.com/cjabradshaw/AusIndigN/tree/main/data">Data</a>
- <em>NppSahul(0-140ka_rawvalues)_Krapp2021.csv</em>: hindcasted net primary production (kg C m<sup>-2</sup> year<sup>-1</sup>) for 0.5°×0.5° grid cells from 140 ka to the present for Sahul from <a href="http://doi.org/10.1038/s41597-021-01009-3">Krapp et al. (2000)</a>
- <em>world2013lifetable.csv</em>: age-specific human life-table values from <a href="http://doi.org/10.1073/pnas.1410465111">Bradshaw & Brook (2014)</a>
- <em>bindensModelOverlay.csv</em>: population estimates from <a href="https://www.ucpress.edu/books/constructing-frames-of-reference/paper">Binford (2001)</a> using R package <code>binford</code> (<a href="http://CRAN.R-project.org/package=binford">Marwick et al. 2016</a>) overlayed on carrying-capacity estimates

## R (v4.3.2) libraries
<a href="https://dplyr.tidyverse.org/"><code>dplyr</code></a> (v1.1.4), <a href="https://plotly.com/r/"><code>plotly</code></a> (v4.10.4), <a href="https://rpkgs.datanovia.com/ggpubr/"><code>ggpubr</code></a> (v0.6.0), <a href="https://cran.r-project.org/web/packages/truncnorm/truncnorm.pdf"><code>truncnorm</code></a> (v1.0-9), <a href="https://cran.r-project.org/web/packages/doSNOW/doSNOW.pdf"><code>doSNOW</code></a> (v1.0.20), <a href="https://cran.r-project.org/web/packages/iterators/iterators.pdf"><code>iterators</code></a> (v1.0.14), <a href="https://cran.r-project.org/web/packages/snow/snow.pdf"><code>snow</code></a> (v0.4-4), <a href="https://cran.r-project.org/web/packages/foreach/vignettes/foreach.html"><code>foreach</code></a> (v1.5.2), <a href="https://cran.r-project.org/web/packages/lhs/vignettes/lhs_basics.html"><code>lhs</code></a> (v1.1.6), <a href="https://cran.r-project.org/web/packages/data.table/vignettes/datatable-intro.html"><code>data.table</code></a> (v1.15.4), <a href="https://cran.r-project.org/web/packages/dismo/dismo.pdf"><code>dismo</code></a> (v1.3-14), <a href="https://cran.r-project.org/web/packages/gbm/gbm.pdf"><code>gbm</code></a> (v2.1.9)

### Acknowledgements
Co-financed by the <a href="https://www.arc.gov.au">Australian Research Council</a> <a href="https://EpicAustralia.org.au">Centre of Excellence for Australian Biodiversity and Heritage</a> (CE170100015) and the <a href="http://ciehf.au">Centre of Excellence for Indigenous and Environmental Histories and Futures</a>.
<br>
<p><a href="https://www.flinders.edu.au"><img align="bottom-left" src="www/Flinders_University_Logo_Stacked_RGB_Master.jpg" alt="Flinders University" height="60" style="margin-top: 20px"></a> <a href="https://globalecologyflinders.com"><img align="bottom-left" src="www/GEL Logo Kaurna New Transp.png" alt="GEL logo" height="55" style="margin-top: 20px"></a> <a href="https://epicaustralia.org.au"><img align="bottom-left" src="www/CabahFCL.cropped.jpg" alt="CABAH" height="50" style="margin-top: 20px"></a> <a href="https://www.jcu.edu.au/"><img align="bottom-left" src="www/CIEHF_Logo_Email_Version Transparent.png" alt="CIEHF" height="45" style="margin-top: 20px"></a> &nbsp; &nbsp; <a href="https://www.jcu.edu.au/"><img align="bottom-left" src="www/JCULogo.webp" alt="James Cook University" height="45" style="margin-top: 20px"></a></p>
