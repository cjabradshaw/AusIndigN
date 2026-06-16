#########################################################################
## Estimating size of pre-colonial Indigenous population in Australia  ##
## August 2024 / updated May 2026                                                         ##
## CJA Bradshaw                                                        ##
#########################################################################

## libraries
library(abind)
library(bootstrap)
library(binford)
library(dismo)
library(gbm)
library(ggplot2)
library(mgcv)
library(ncdf4)
library(oceanmap)
library(OceanView)
library(performance)
library(pracma)
library(raster)
library(rgl)
library(sp)
library(scatterplot3d) 
library(sdep)
library(sjPlot)
library(sp)
library(spatialEco)
library(SpatialPack)
library(spatstat)
library(terra)
library(truncnorm)

## source functions
setwd("~/Documents/GitHub/AusIndigN/scripts/source")
source("matrixOperators.r")
source("new_lmer_AIC_tables3.R") 
source("r.squared.R") 

## custom functions
# gradient function for immigration
# pI ~ a / (1 + (b * exp(-c * Rk)))
aI <- 0.95; bI <- 5000; cI <- 3
pI.func <- function(Rk) {
  pI <- aI / (1 + (bI * exp(-cI * Rk)))
  return(pI)}
pI.func(4)
xI <- seq(1,10,0.01)
yI <- pI.func(xI)

# gradient function for emigration
aE <- 1; bE <- -3.2
pE.func <- function(Rk) {
  pE <- aE * exp(bE * Rk)
  return(pE)}
pE.func(0.5)
xE <- seq(0.01,1,0.01)
yE <- pE.func(xE)
pE.out <- data.frame(xE,yE)

# stochastic beta sampler (single sample)
stoch.beta.func <- function(mu, var) {
  Sx <- rbeta(length(mu), (((1 - mu) / var - 1 / mu) * mu ^ 2), ((((1 - mu) / var - 1 / mu) * mu ^ 2)*(1 / mu - 1)))
  return(params=Sx)
}

# stochastic beta sampler (n samples)
stoch.n.beta.func <- function(n, mu, var) {
  Sx <- rbeta(n, (((1 - mu) / var - 1 / mu) * mu ^ 2), ((((1 - mu) / var - 1 / mu) * mu ^ 2)*(1 / mu - 1)))
  return(params=Sx)
}

# dynamics model function
Nproj.func <- function(Nt, rm, K) {
  Nt1 <- round(Nt * exp(rm*(1-(Nt/K))), 0)
  return(Nt1)
}

# rescale a range
rscale <- function (x, nx1, nx2, minx, maxx) {
  nx = nx1 + (nx2 - nx1) * (x - minx)/(maxx - minx)
  return(nx)
}

# matrix rotation
rot.mat <- function(x) t(apply(x, 2, rev))

# matrix poisson resampler
rpois.fun <- function(x,y,M) {
  rpois(1,M[x,y])
}
rpois.vec.fun <- Vectorize(rpois.fun,vectorize.args = c('x','y'))

## list coordinates to xyz
coordlist2xyz <- function (list) {
  rl <- length(list[[1]]); cl <- length(list[[2]])
  coords <- c(NA,NA)
  for (r in 1:rl) {
    for (c in 1:cl) {
      coords <- rbind(coords, c(list[[1]][r],list[[2]][c]))
    }
  }
  coords <- coords[-1,]
  return(coordxyz=coords)
}

# AIC corrected for small n
AICc <- function(...) {
  models <- list(...)
  num.mod <- length(models)
  AICcs <- numeric(num.mod)
  ns <- numeric(num.mod)
  ks <- numeric(num.mod)
  AICc.vec <- rep(0,num.mod)
  for (i in 1:num.mod) {
    if (length(models[[i]]$df.residual) == 0) n <- models[[i]]$dims$N else n <- length(models[[i]]$residuals)
    if (length(models[[i]]$df.residual) == 0) k <- sum(models[[i]]$dims$ncol) else k <- (length(models[[i]]$coeff))+1
    AICcs[i] <- (-2*logLik(models[[i]])) + ((2*k*n)/(n-k-1))
    ns[i] <- n
    ks[i] <- k
    AICc.vec[i] <- AICcs[i]
  }
  return(AICc.vec)
}

# information-criteria functions
delta.IC <- function(x) x - min(x) ## where x is a vector of an IC
weight.IC <- function(x) (exp(-0.5*x))/sum(exp(-0.5*x)) ## Where x is a vector of dIC
ch.dev <- function(x) ((( as.numeric(x$null.deviance) - as.numeric(x$deviance) )/ as.numeric(x$null.deviance))*100) ## % change in deviance, where x is glm object

# evidence ratio
linreg.ER <- function(x,y) { # where x and y are vectors of the same length; calls AICc, delta.AIC, weight.AIC functions
  fit.full <- lm(y ~ x); fit.null <- lm(y ~ 1)
  AIC.vec <- c(AICc(fit.full),AICc(fit.null))
  dAIC.vec <- delta.IC(AIC.vec); wAIC.vec <- weight.IC(dAIC.vec)
  ER <- wAIC.vec[1]/wAIC.vec[2]
  r.sq.adj <- as.numeric(summary(fit.full)[9])
  return(c(ER,r.sq.adj))
}

################################
## estimating carrying capacity
################################

## set grids

## NPP (HadCM3)
setwd("~/Documents/GitHub/AusIndigN/data")
nppH <- read.table("NppSahul(0-140ka_rawvalues)_Krapp2021.csv", header=T, sep=",") # 0.5 deg lat resolution
not.naH <- which(is.na(nppH[,3:dim(nppH)[2]]) == F, arr.ind=T)
upper.rowH <- as.numeric(not.naH[1,1])
lower.rowH <- as.numeric(not.naH[dim(not.naH)[1],1])
min.latH <- max(nppH[not.naH[,1], 1])  
max.latH <- min(nppH[not.naH[,1], 1])
min.lonH <- min(nppH[not.naH[,1], 2])
max.lonH <- max(nppH[not.naH[,1], 2])

sahul.subH <- rep(0, dim(nppH)[1])
for (n in 1:dim(nppH)[1]) {
  sahul.subH[n] <- ifelse(nppH[n,1] <= min.latH & nppH[n,1] >= max.latH & nppH[n,2] >= min.lonH & nppH[n,2] <= max.lonH, 1, 0)
}  
sah.keepH <- which(sahul.subH == 1)
nppH.sah <- nppH[sah.keepH,]

# Siler hazard h(x) (Gurven et al. 2007)
# average hunter-gatherer
a1 <- 0.422 # initial infant mortality rate (also known as αt)
b1 <- 1.131 # rate of mortality decline (also known as bt)
a2 <- 0.013 # age-independent mortality (exogenous mortality due to environment); also known as ct
a3 <- 1.47e-04 # initial adult mortality rate (also known as βt)
b3 <- 0.086 # rate of mortality increase
longev <- 80
x <- seq(0,longev,1) # age vector
h.x <- a1 * exp(-b1*x) + a2 + a3 * exp(b3 * x) # Siler's hazard model
l.x <- exp((-a1/b1) * (1 - exp(-b1*x))) * exp(-a2 * x) * exp(a3/b3 * (1 - exp(b3 * x))) # Siler's survival (proportion surviving) model

l.inf <- exp(-a1/b1) # survival at infinite time
T.m <- 1/b1 # time constant at which maturity is approached
h.m <- a2 # hazard for mature animals
l.m <- exp(-a2*x) # survival
h.s <- a3*exp(b3*x) # hazard for senescence
l.s <- exp((a3/b3)*(1 - exp(b3*x))) # survival for senescence
f.x <- a3*exp(b3*x)*exp((a3/b3)/(1-exp(b3*x))) # probability density function
(log(a3) - log(a1)) / a3
T.s <- (1/b3) # modal survival time

## survival
init.pop <- 10000
lx <- round(init.pop*l.x,0)
len.lx <- length(lx)
dx <- lx[1:(len.lx-1)]-lx[2:len.lx]
qx <- dx/lx[1:(length(lx)-1)]
Sx <- 1 - qx
sx <- lx[2:len.lx]/lx[1:(len.lx-1)]
mx <- 1 - sx
Lx <- (lx[1:(len.lx-1)] + lx[2:len.lx])/2
ex <- rev(cumsum(rev(Lx)))/lx[-len.lx]
ex.avg <- ex + x[-len.lx]

# set SD for Sx
Sx.sd <- 0.05 # can set to any value

# fertility (Walker et al. 2006)
primiparity.walker <- c(17.7,18.7,19.5,18.5,18.5,18.7,25.7,19,20.5,18.8,17.8,18.6,22.2,17,16.2,18.4)
prim.mean <- round(mean(primiparity.walker),0)
prim.lo <- round(quantile(primiparity.walker,probs=0.025),0)
prim.hi <- round(quantile(primiparity.walker,probs=0.975),0)
dat.world13 <- read.table("world2013lifetable.csv", header=T, sep=",")
fert.world13 <- dat.world13$m.f
fert.trunc <- fert.world13[1:(longev+1)]
pfert.trunc <- fert.trunc/sum(fert.trunc)
fert.bentley <- 4.69/2 # Bentley 1985 for !Kung
fert.vec <- fert.bentley * pfert.trunc

## construct matrix
stages <- len.lx
popmat <- matrix(0,nrow=stages,ncol=stages)
colnames(popmat) <- x
rownames(popmat) <- x

## populate matrix
popmat[1,] <- fert.vec
diag(popmat[2:stages,]) <- Sx
popmat[stages,stages] <- 0 # Sx[stages-1]
popmat.orig <- popmat ## save original matrix

## matrix properties
r.ann <- max.r(popmat) # rate of population change, 1-yr
#stable.stage.dist(popmat) ## stable stage distribution
R.val(popmat,stages) # reproductive value
gen.l <- G.val(popmat,stages) # mean generation length

## for r.max (set Sx=1)
Sx.1 <- Sx
Sx.1[] <- 1
popmat.max <- popmat.orig
diag(popmat.max[2:stages,]) <- Sx.1
popmat.max[stages,stages] <- 0 # Sx[stages-1]
max.lambda(popmat.max) ## 1-yr lambda
rm.ann <- max.r(popmat.max) # rate of population change, 1-yr

#stable.stage.dist(popmat) ## stable stage distribution
R.val(popmat,stages) # reproductive value
gen.l <- G.val(popmat,stages) # mean generation length

### population dynamics parameters
# dynamical model
# Nt+1 = Nt * exp(rm*(1-(Nt/K))) - (E - I)
lambda.ann <- exp(r.ann) # annual lambda
r.max.NEE <- 2 * log(lambda.ann^gen.l) # human rmax at generational scale (arbitrarily double)
lambda.max.ann <- exp(rm.ann)
rm.max.NEE <- log(lambda.max.ann^gen.l) # human rmax at generational scale (from Sx=1 Leslie matrix)

# Cole's allometric calculation (high)
alpha.Ab <- 15
a.Cole <- -0.16
a.lo.Cole <- -0.41
a.up.Cole <- 0.10
a.sd.Cole <- mean(c((a.Cole - a.lo.Cole)/1.96, (a.up.Cole - a.Cole)/1.96))
b.lo.Cole <- -1.2
b.up.Cole <- -0.79
b.Cole <- -0.99
b.sd.Cole <- mean(c((b.Cole - b.lo.Cole)/1.96, (b.up.Cole - b.Cole)/1.96))
r.max.Cole <- 10^(a.Cole + b.Cole*log10(alpha.Ab)) # from Hone et al. 2003-JApplEcol
r.max.lo.Cole <- 10^(a.lo.Cole + b.lo.Cole*log10(alpha.Ab))
r.max.up.Cole <- 10^(a.up.Cole + b.up.Cole*log10(alpha.Ab))

r.max.up.gen.Cole <- log((exp(r.max.up.Cole))^gen.l)
r.max.gen.Cole <- log((exp(r.max.Cole))^gen.l)
r.max.lo.gen.Cole <- log((exp(r.max.lo.Cole))^gen.l)
r.max.gen.Cole.sd <- mean(c((r.max.gen.Cole - r.max.lo.gen.Cole)/1.96, (r.max.up.gen.Cole - r.max.gen.Cole)/1.96))


    ### relationship between NPP and K
    K.NPP <- "rotated parabolic"

    # npp @ modern
    sub.modH <- which(colnames(nppH.sah) == paste("X",0,sep=""))
    nppH.sah.mod <- nppH.sah[,c(1,2,sub.modH)]
    
    # plot raster
    coordinates(nppH.sah.mod) = ~ Lon + Lat
    proj4string(nppH.sah.mod)=CRS("+proj=longlat +datum=WGS84") # set it to lat-long
    gridded(nppH.sah.mod) = TRUE
    nppH.mod = raster(nppH.sah.mod)

    lim.exts <- 5

    lzH <- dim(nppH.sah)[2] - 2
    nppH.array <- array(data=NA, dim=c(dim(raster2matrix(nppH.mod)),lzH))
    for (k in 3:(lzH+2)) {
      nppH.sah.k <- nppH.sah[,c(1,2,k)] 
      coordinates(nppH.sah.k) = ~ Lon + Lat
      proj4string(nppH.sah.k)=CRS("+proj=longlat +datum=WGS84") # set it to lat-long
      gridded(nppH.sah.k) = TRUE
      nppH.k = raster(nppH.sah.k)
      nppH.array[,,k-2] <- raster2matrix(nppH.k)
    }
    image((nppH.array[,,5]), col=rev(grey(1:100/100)))
    
    ## NPP temporal outputs 40 ka—present
    t1000Hvec <- 0:40
    nppH.array.40pres <- nppH.array[,,1:length(t1000Hvec)]
    dim(nppH.array.40pres)
    image((nppH.array.40pres[,,1]), col=rev(grey(1:100/100)))

    AUS.nppH.array.40pres1 <- nppH.array.40pres[, 1:66, ]
    dim(AUS.nppH.array.40pres1)
    AUS.nppH.array.40pres <- AUS.nppH.array.40pres1[-c(88),-c(65:66),]
    dim(AUS.nppH.array.40pres)
    AUS.nppH.array.40pres[87,64,1] <- NA
    AUS.nppH.array.pres <- AUS.nppH.array.40pres[,,1]
    dim(AUS.nppH.array.pres)
    image(AUS.nppH.array.40pres[,,1], col=rev(grey(1:100/100)))

    # Tasmania, not including Bass Strait islands Jones, Blomely, Reynolds, O'Ryan (estimates for pre-contact)
    # 42° 01' 17" South, 146° 35' 36":  42+(01/60)+(17/(60*60)) = -42.02; 146+(35/60)+(36/(60*60)) = 146.5933
    TAS.nppH.array.pres <- AUS.nppH.array.pres[69:77,1:6]
    TAS.nppH.array.40pres <- AUS.nppH.array.40pres[69:77,1:6,]
    image(TAS.nppH.array.pres, col=rev(grey(1:100/100)))
    
    # full area
    ALL.nppH.40pres <- apply(nppH.array.40pres, 3, mean, na.rm=T)
    length(ALL.nppH.40pres)
    plot(t1000Hvec,ALL.nppH.40pres, type="l")

    # AUS
    AUS.nppH.40pres <- apply(AUS.nppH.array.40pres, 3, mean, na.rm=T)
    length(AUS.nppH.40pres)
    plot(t1000Hvec,AUS.nppH.40pres, type="l")
    
    # TAS
    TAS.nppH.40pres <- apply(TAS.nppH.array.40pres, 3, mean, na.rm=T)
    length(TAS.nppH.40pres)
    plot(t1000Hvec,TAS.nppH.40pres, type="l")
    
    ## calculate all Ks as relative to current
    nppH.AUS.rel <- AUS.nppH.array.40pres
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      nppH.AUS.rel[,,z] <- AUS.nppH.array.40pres[,,z] / AUS.nppH.array.40pres[,,1]
    }
    nppH.AUS.rel[,,1] <- AUS.nppH.array.40pres[,,1]
    
    nppH.TAS.rel <- TAS.nppH.array.40pres
    for (z in 1:dim(TAS.nppH.array.40pres)[3]) {
      nppH.TAS.rel[,,z] <- TAS.nppH.array.40pres[,,z] / TAS.nppH.array.40pres[,,1]
    }
    nppH.TAS.rel[,,1] <- TAS.nppH.array.40pres[,,1]
    
    # npp to K
    hum.dens.med <- 6.022271e-02
    hum.dens.lq <- 3.213640e-02
    hum.dens.uq <- 1.439484e-01
    hum.dens.max <- 1.152206e+00
    hum.dens.min <- 1.751882e-02
    cell.area <- (111.12/2)*(111.12/2) # km2
    
    # modify underlying K magnitude by modifying NPP across the board
    K.array <- nppH.AUS.rel
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.array[,,z] <- rscale(AUS.nppH.array.40pres[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(AUS.nppH.array.40pres[,,z], na.rm=T), max(AUS.nppH.array.40pres[,,z], na.rm=T))
    }

    # 180-deg rotated parabola
    # y = a(x - h)^2 + k
    # h = median NPP; k = max K; a = negative for 180 flipped
    k.Kmax <- max(K.array, na.rm=T)/2
    h.NPPmed <- mean(AUS.nppH.array.40pres, na.rm=T)
    h.NPPmed <- mean(range(AUS.nppH.array.40pres, na.rm=T))
    Kmin <- min(K.array, na.rm=T)
    NPP.seq <- seq(min(AUS.nppH.array.40pres, na.rm=T), max(AUS.nppH.array.40pres, na.rm=T), 0.01)
    K.parab.pred <- (-3 * (NPP.seq - h.NPPmed)^2) + k.Kmax
    K.parab.pred.rescale <- rscale(K.parab.pred, round(hum.dens.min*cell.area, 0), 0.5*round(hum.dens.max*cell.area, 0), min(K.parab.pred), max(K.parab.pred))

    K.lin.x <- c(min(AUS.nppH.array.40pres, na.rm=T), max(AUS.nppH.array.40pres, na.rm=T))
    K.lin.y <- c(min(K.array, na.rm=T), max(K.array, na.rm=T))
    fit.K.lin <- lm(K.lin.y ~ K.lin.x)
    K.lin.pred <- as.numeric(coef(fit.K.lin)[1]) + as.numeric(coef(fit.K.lin)[2])*NPP.seq
    
    # rotated parabolic
    K.array.parab <- (-3 * (AUS.nppH.array.40pres - h.NPPmed)^2) + k.Kmax
    K.array.parab.rescale <- K.array.parab
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.array.parab.rescale[,,z] <- rscale(K.array.parab[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(K.array.parab[,,z], na.rm=T), max(K.array.parab[,,z], na.rm=T))
    }

    # rescale so that parabolic total K = linear total K
    hist.K.array <- hist(K.array, br=12)
    hist.K.array.dat <- data.frame(hist.K.array$mids, hist.K.array$density)
    
    # rescale K.array.parab.rescale to same sum as K.array (distribution of Ks = same total)
    K.array.parab.rescale2 <- K.array.parab.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    dim(K.array.parab.rescale2)
    sum(K.array.parab.rescale2, na.rm=T)
    
    hist.K.parab.pred.rescale2 <- hist(K.array.parab.rescale2,br=12)
    hist.K.parab.pred.rescale2.dat <- data.frame(hist.K.parab.pred.rescale2$mids, hist.K.parab.pred.rescale2$density)

    # rotate matrix -90 & renumber from oldest to youngest
    if (K.NPP == "rotated parabolic") {
      K.array.use <- K.array.parab.rescale
    }
    
    K.rot.array <- array(data=NA, c(dim(K.array.use)[2], dim(K.array.use)[1], lzH))
    for (z in 1:dim(AUS.nppH.array.40pres)[3]) {
      K.rot.array[,,z] <- apply(t(K.array.use[,,42-z]),2,rev)
    }
    image(rot.mat(K.rot.array[,,41]))

    # population estimate 
    dim(K.rot.array)
    Kmod.array <- K.rot.array[,,41]
    sum(K.rot.array[,,41], na.rm=T)
    image(rot.mat(Kmod.array))

    # Tasmania estimate
    dim(K.rot.array)
    image(rot.mat(K.rot.array[60:64, 69:77, 41]))
    round(sum(K.rot.array[60:64, 69:77, 41], na.rm=T), 0)
    
    ## create & export rasters
    lat.vec <- -seq(11.5,43,0.5)
    lon.vec <- seq(110.5,153.5,0.5)
    llat <- length(lat.vec)
    llon <- length(lon.vec)
    llat*llon
    dim(Kmod.array)[1] * dim(Kmod.array)[2] 
    
    Kxyz <- matrix(data=NA,nrow=1,ncol=3)
    for (i in 1:llat) {
      for (j in 1:llon) {
        Kxyz <- rbind(Kxyz, c(lon.vec[j],lat.vec[i],Kmod.array[i,j]))
      }
    }
    
    Kxyz <- Kxyz[-1,]
    K.xyz <- as.data.frame(Kxyz)
    colnames(K.xyz) <- c("x","y","K")
    head(K.xyz)
    K.rast <- rasterFromXYZ(K.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((K.rast))
    writeRaster(K.rast, filename="KparaMod.grd", format="raster", overwrite=T)
    
    Nprp.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "Nprp"=K.xyz$K/(sum(K.xyz$K, na.rm=T)))
    head(Nprp.xyz)
    hist(Nprp.xyz$Nprp)
    
    N2M.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "N2M"=2e6*Nprp.xyz$Nprp)
    N3M.xyz <- data.frame("x"=K.xyz$x, "y"=K.xyz$y, "N2M"=3e6*Nprp.xyz$Nprp)
    
    write.csv(N2M.xyz, "N2Mxyz.csv")
    write.csv(N3M.xyz, "N3Mxyz.csv")
    
    N2M.rast <- rasterFromXYZ(N2M.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((N2M.rast))
    writeRaster(N2M.rast, filename="N2M.grd", format="raster", overwrite=T)
    
    N3M.rast <- rasterFromXYZ(N3M.xyz, crs=CRS("+proj=longlat +datum=WGS84"))
    plot((N3M.rast))
    writeRaster(N3M.rast, filename="N3M.grd", format="raster", overwrite=T)
    
    ## SAHUL
    ## calculate all Ks as relative to current
    nppH.rel <- nppH.array.40pres
    for (z in 1:dim(nppH.array.40pres)[3]) {
      nppH.rel[,,z] <- nppH.array.40pres[,,z] / nppH.array.40pres[,,1]
    }
    nppH.rel[,,1] <- nppH.array.40pres[,,1]
    
    # modify underlying K magnitude by modifying NPP across the board
    K.array <- nppH.rel
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.array[,,z] <- rscale(nppH.array.40pres[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(nppH.array.40pres[,,z], na.rm=T), max(nppH.array.40pres[,,z], na.rm=T))
    }
    
    # 180-deg rotated parabola
    # y = a(x - h)^2 + k
    # h = median NPP; k = max K; a = negative for 180 flipped
    k.Kmax <- max(K.array, na.rm=T)/2
    h.NPPmed <- mean(nppH.array.40pres, na.rm=T)
    h.NPPmed <- mean(range(nppH.array.40pres, na.rm=T))
    Kmin <- min(K.array, na.rm=T)
    NPP.seq <- seq(min(nppH.array.40pres, na.rm=T), max(nppH.array.40pres, na.rm=T), 0.01)
    K.parab.pred <- (-3 * (NPP.seq - h.NPPmed)^2) + k.Kmax
    K.parab.pred.rescale <- rscale(K.parab.pred, round(hum.dens.min*cell.area, 0), 0.5*round(hum.dens.max*cell.area, 0), min(K.parab.pred), max(K.parab.pred))
    
    K.lin.x <- c(min(nppH.array.40pres, na.rm=T), max(nppH.array.40pres, na.rm=T))
    K.lin.y <- c(min(K.array, na.rm=T), max(K.array, na.rm=T))
    fit.K.lin <- lm(K.lin.y ~ K.lin.x)
    K.lin.pred <- as.numeric(coef(fit.K.lin)[1]) + as.numeric(coef(fit.K.lin)[2])*NPP.seq
    
    # rotated parabolic
    K.array.parab <- (-3 * (nppH.array.40pres - h.NPPmed)^2) + k.Kmax
    K.array.parab.rescale <- K.array.parab
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.array.parab.rescale[,,z] <- rscale(K.array.parab[,,z], round(hum.dens.min*cell.area, 0), round(hum.dens.max*cell.area, 0), min(K.array.parab[,,z], na.rm=T), max(K.array.parab[,,z], na.rm=T))
    }
    
    # rescale so that parabolic total K = linear total K
    hist.K.array <- hist(K.array, br=12)
    hist.K.array.dat <- data.frame(hist.K.array$mids, hist.K.array$density)
    
    # rescale K.array.parab.rescale to same sum as K.array (distribution of Ks = same total)
    K.array.parab.rescale2 <- K.array.parab.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    sum(K.array.parab.rescale2, na.rm=T)
    
    K.parab.pred.rescale2 <- K.parab.pred.rescale / (sum(K.array.parab.rescale, na.rm=T)/sum(K.array, na.rm=T))
    hist.K.parab.pred.rescale2 <- hist(K.parab.pred.rescale2,br=12)
    hist.K.parab.pred.rescale2.dat <- data.frame(hist.K.parab.pred.rescale2$mids, hist.K.parab.pred.rescale2$density)
    
    # rotate matrix -90 & renumber from oldest to youngest
    if (K.NPP == "rotated parabolic") {
      K.array.use <- K.array.parab.rescale
    }
    
    K.rot.array <- array(data=NA, c(dim(K.array.use)[2], dim(K.array.use)[1], lzH))
    for (z in 1:dim(nppH.array.40pres)[3]) {
      K.rot.array[,,z] <- apply(t(K.array.use[,,42-z]),2,rev)
    }
    
    # population estimate 
    Kmod.array <- K.rot.array[,,1]
    sum(K.rot.array[,,1], na.rm=T)
    
    
    ################################################################################   
    ## historically reported population sizes vs. carrying capacity-predicted sizes
    ################################################################################   
    
    # 10, 59
    # -17.067, 139.497 (Bentinck Island, Carpentaria) # Tindale 1962
    # 1910-1940: 103 to 123 people
    BI.crds <- rbind(coordlist2xyz(list(34, 59))) # Bentinck Island
    BI.K.cell <- K.rot.array[BI.crds[1,1], BI.crds[1,2], 1]
    BI.K.cell
    round(150/cell.area * BI.K.cell, 0)
    
    BI.cellN <- 3491
    BI.cellD <- BI.cellN/cell.area
    BI.predN <- BI.cellD * 150
    round(BI.predN, 0)
    
    # -40.692, 144.944 (Robbins Island, Tasmania): 50 people (Kelly in 1816, Baudin 1964)
    RI.crds <- rbind(coordlist2xyz(list(82, 70)))
    RI.K.cell <- K.rot.array[RI.crds[1,1], RI.crds[1,2], 1]
    RI.K.cell
    round(99/cell.area * RI.K.cell, 0)
    
    # -33.993, 151.17 (Botany Bay, NSW) # from Shane Ingrey: 400 people 
    BB.crds <- rbind(coordlist2xyz(list(68, 82)))
    BB.K.cell <- K.rot.array[BB.crds[1,1], BB.crds[1,2], 1]
    BB.K.cell
    round(416/cell.area * BB.K.cell, 0)
    
    BB.cellN <- 3548
    BB.cellD <- BB.cellN/cell.area
    BB.predN <- BB.cellD * 416
    round(BB.predN, 0)
    
    
    # -25.802, 113.025 (Dorre & Bernier Islands, WA); 100 km2, 40 people
    DH.crds <- rbind(coordlist2xyz(list(52, 7)))
    DH.K.cell <- K.rot.array[DH.crds[1,1], DH.crds[1,2], 1]
    DH.K.cell
    round(100/cell.area * DH.K.cell, 0)
    
    DBI.cellN <- 1331
    DBI.cellD <- DBI.cellN/cell.area
    DBI.predN <- DBI.cellD * 100
    round(DBI.predN, 0)
    
    # Botany Bay Kurnel Meeting Place -34 00 09" / 151 13" 15.6" ("no more than forty")
    # 24.11 km2; First Fleet observation
    # 34+(9/60/60) = -34.0025; 151+(13/60)+(15.6/(60*60)) = 151.221
    BBKMP.crds <- rbind(coordlist2xyz(list(68, 82)))
    BBKMP.K.cell <- K.rot.array[BBKMP.crds[1,1], BBKMP.crds[1,2], 1]
    BBKMP.K.cell
    round(24.11/cell.area * BBKMP.K.cell, 0)
    
    BBKMP.cellN <- 3548
    BBKMP.cellD <- BBKMP.cellN/cell.area
    BBKMP.predN <- BBKMP.cellD * 24.11
    round(BBKMP.predN, 0)
    
    # Sydney Cove
    # "Their number in the neighbourhood of this settlement, that is within ten miles (16 km) to
    # the northward and ten miles to the southward, I reckon at fifteen hundred.
    # Governor Phillip to Lord Sydney, 10 July 1788, in Historical Records of Australia,
    # Volume 1, 1788-1796, Governor's Despatches to and from England
    # (Sydney: The Library Committee of the Commonwealth Parliament, 1914), p. 65.
    # 151.2200032,	-33.86924628; area with 16 km buffer = 111.32^2 * 0.03944372784279604 = 489
    SC.cellN <- 3548
    SC.cellD <- SC.cellN/cell.area
    SC.predN <- SC.cellD * 489
    round(SC.predN, 0)
    
    # Possession Island, -10.72 / 142.40, 10 men, 5 km2 (Flinders referencing Cook)
    PI.crds <- rbind(coordlist2xyz(list(22, 64)))
    PI.K.cell <- K.rot.array[PI.crds[1,1], PI.crds[1,2], 1]
    PI.K.cell
    round(5/cell.area * PI.K.cell, 0)
    
    PI.cellN <- 3001
    PI.cellD <- PI.cellN/cell.area
    PI.predN <- PI.cellD * 5
    round(PI.predN, 0)
    
    # Darling (Erub) Island -9.59, 143.76, 5.7 km2, 80-90 people (Flinders 1803)
    EI.crds <- rbind(coordlist2xyz(list(19, 68)))
    EI.K.cell <- K.rot.array[EI.crds[1,1], EI.crds[1,2], 1]
    EI.K.cell
    round(5.7/cell.area * EI.K.cell, 0)

    
    ############################
    # analysis of Binford data #
    ############################
    
    bindens <- data.frame("GN"=LRB$groupno, "year"=LRB$year, "lon"=LRB$longitude, "lat"=LRB$latitude, "area"=LRB$area,
                          "pdens"=LRB$density/100)
    write.table(bindens, "bindens.csv", sep=",", row.names = F)
    
    bindensModOverl <- read.csv("bindensModelOverlay.csv")
    
    plot(bindensModOverl$pdens, bindensModOverl$modD, pch=19, ylab="model", xlab="Binford", xlim=c(0,1.2), ylim=c(0,1.2))
    bindensMod.fit <- lm(modD ~ pdens, data=bindensModOverl)
    summary(bindensMod.fit)    
    abline(bindensMod.fit, col="red", lty=2, lwd=2)
    xy121 <- data.frame("x"=seq(0,1.2,0.01), "y"=seq(0,1.2,0.01))
    lines(xy121[,1],xy121[,2], lty=2, lwd=2)
    range(bindensModOverl$year)
    median(bindensModOverl$year)
    
    hist(bindensModOverl$pdens)
    hist(bindensModOverl$modD)
    
    bindensModOverl$DratioM2B <- bindensModOverl$modD/bindensModOverl$pdens
    hist((bindensModOverl$DratioM2B))
    hist(log10(bindensModOverl$DratioM2B))
    1/exp(mean(log(bindensModOverl$DratioM2B)))
    
    # generalised linear models
    head(bindensModOverl)
    hist(bindensModOverl$year)
    plot(bindensModOverl$year, bindensModOverl$pdens, xlab="year", ylab="Binford D", pch=19)
    plot(bindensModOverl$year, (bindensModOverl$DratioM2B), xlab="year", ylab="model D:Binford D", pch=19)
    
    # model set
    m1 <- "pdens ~ modD + year"
    m2 <- "pdens ~ modD"
    m3 <- "pdens ~ year"
    m4 <- "pdens ~ 1"
    
    ## model vector
    mod.vec <- c(m1,m2,m3,m4)
    length(mod.vec)
    length(unique(mod.vec))
    
    ## define n.mod
    n.mod <- length(mod.vec)
    
    # model fitting and logLik output loop
    Modnum <- length(mod.vec)
    LL.vec <- SaveCount <- AICc.vec <- BIC.vec <- k.vec <- terml <- Rm <- Rc <- rep(0,Modnum)
    mod.list <- summ.fit <- coeffs <- coeffs.se <- term.labs <- coeffs.st <- list()
    mod.num <- seq(1,Modnum,1)
    
    for(i in 1:Modnum) {
      fit <- glm(as.formula(mod.vec[i]),family=Gamma(link="log"), data=bindensModOverl, na.action=na.omit)
      assign(paste("fit",i,sep=""), fit)
      mod.list[[i]] <- fit
      print(i)
    }
    
    sumtable <- aicW(mod.list, finite = TRUE, null.model = NULL, order = F)
    row.names(sumtable) <- mod.vec
    summary.table <- sumtable[order(sumtable[,7],decreasing=F),]
    summary.table
    
    ## saturated residual diagnostic
    i <- 1
    fit <- glm(as.formula(mod.vec[i]),family=Gamma(link="log"), data=bindensModOverl, na.action=na.omit)

    check_model(fit, detrend=F)
    plot_model(fit, show.values=T, vline.color = "purple")
    
    # BRT
    dim(bindensModOverl)[1]
    hist(bindensModOverl$DratioM2B)
    bindensModOverl$DratioM2B.sc <- scale(bindensModOverl$DratioM2B, center=T, scale=T)
    bindensModOverl$DratioM2B.lg10 <- log10(bindensModOverl$DratioM2B)
    bindensModOverl$neglat.sc <- scale(-bindensModOverl$lat, center=T, scale=T)
    bindensModOverl$year.sc <- scale(bindensModOverl$year, center=T, scale=T)
    head(bindensModOverl)
    
    brt.fit <- gbm.step(bindensModOverl, gbm.x = attr(bindensModOverl, "names")[c(2,4)],
                        gbm.y = attr(bindensModOverl, "names")[11], 
                        family="gaussian", max.trees=100000, tolerance = 0.0002, learning.rate = 0.00025, 
                        bag.fraction=0.75, tree.complexity = 2)
    summary(brt.fit)
    gbmpl <- gbm.plot(brt.fit, smooth=T, n.plots=2, common.scale=T, y.label="log10 model D:Binford D", plot.layout = c(1,2),
             show.contrib = T, rug=T)
    gbm.plot.fits(brt.fit)
    brt.fit$fitted.vars
    
    par(mfrow=c(1,2))
    x2 <- plot.gbm(brt.fit, i.var=brt.fit$var.names[2], continuous.resolution=100, return.grid=T)[,1]
    y2 <- 10^plot.gbm(brt.fit, i.var=brt.fit$var.names[2], continuous.resolution=100, return.grid=T)[,2]
    plot(x2,y2,type="l", xlab=brt.fit$var.names[2], ylab="model D:Binford D", ylim=c(0,40))
    x1 <- plot.gbm(brt.fit, i.var=brt.fit$var.names[1], continuous.resolution=100, return.grid=T)[,1]
    y1 <- 10^plot.gbm(brt.fit, i.var=brt.fit$var.names[1], continuous.resolution=100, return.grid=T)[,2]
    plot(x1,y1,type="l", xlab=brt.fit$var.names[1], ylab="model D:Binford D", ylim=c(0,40))
    par(mfrow=c(1,1))
    
    BRTmodDBinD.dat <- data.frame("latx"=x2, "laty"=y2, "yearx"=x1, "yeary"=y1)
    write.table(BRTmodDBinD.dat, "BRTmodDBinD.csv", sep=",", row.names = F)
    
    CV.cor <- fitted.varsCV.cor <- 100 * brt.fit$cv.statistics$correlation.mean
    CV.cor.se <- 100 * brt.fit$cv.statistics$correlation.se
    print(c(CV.cor, CV.cor.se))
    
    ########################################
    # generalised additive model analogue ##
    ########################################
    DratioM2B.sc.center <- as.numeric(attr(bindensModOverl$DratioM2B.sc, "scaled:center"))
    DratioM2B.sc.scale <- as.numeric(attr(bindensModOverl$DratioM2B.sc, "scaled:scale"))
    
    gam.fit <- mgcv::gam(
      DratioM2B.sc ~
        s(year, k = 10) +
        s(lat, k = 10),
      data = bindensModOverl,
      family = gaussian(),
      method = "REML"
    )
    summary(gam.fit)
    mgcv::gam.check(gam.fit)
    
    back.transform.Dratio <- function(x) {
      (x * DratioM2B.sc.scale) + DratioM2B.sc.center
    }
    
    mean.year <- mean(bindensModOverl$year, na.rm=T)
    mean.lat <- mean(bindensModOverl$lat, na.rm=T)
    
    gam.year.grid <- data.frame(
      year = seq(min(bindensModOverl$year, na.rm=T), max(bindensModOverl$year, na.rm=T), length.out=100),
      lat = mean.lat
    )
    gam.lat.grid <- data.frame(
      year = mean.year,
      lat = seq(min(bindensModOverl$lat, na.rm=T), max(bindensModOverl$lat, na.rm=T), length.out=100)
    )
    
    gam.year.pred <- predict(gam.fit, newdata = gam.year.grid, type = "response", se.fit = TRUE)
    gam.lat.pred <- predict(gam.fit, newdata = gam.lat.grid, type = "response", se.fit = TRUE)
    
    gam.year.fit <- back.transform.Dratio(as.numeric(gam.year.pred$fit))
    gam.year.lo <- back.transform.Dratio(as.numeric(gam.year.pred$fit - 1.96 * gam.year.pred$se.fit))
    gam.year.up <- back.transform.Dratio(as.numeric(gam.year.pred$fit + 1.96 * gam.year.pred$se.fit))
    
    gam.lat.fit <- back.transform.Dratio(as.numeric(gam.lat.pred$fit))
    gam.lat.lo <- back.transform.Dratio(as.numeric(gam.lat.pred$fit - 1.96 * gam.lat.pred$se.fit))
    gam.lat.up <- back.transform.Dratio(as.numeric(gam.lat.pred$fit + 1.96 * gam.lat.pred$se.fit))
    
    par(mfrow=c(1,2))
    plot(gam.lat.grid$lat, gam.lat.fit, type="l", xlab="lat", ylab="model D:Binford D",
         ylim=c(min(gam.lat.lo, na.rm=T), max(gam.lat.up, na.rm=T)))
    lines(gam.lat.grid$lat, gam.lat.lo, lty=2, col="red")
    lines(gam.lat.grid$lat, gam.lat.up, lty=2, col="red")
    plot(gam.year.grid$year, gam.year.fit, type="l", xlab="year", ylab="model D:Binford D",
         ylim=c(min(gam.year.lo, na.rm=T), max(gam.year.up, na.rm=T)))
    lines(gam.year.grid$year, gam.year.lo, lty=2, col="red")
    lines(gam.year.grid$year, gam.year.up, lty=2, col="red")
    par(mfrow=c(1,1))
    
    GAMmodDBinD.dat <- data.frame(
      "latx"=gam.lat.grid$lat,
      "laty"=gam.lat.fit,
      "laty.lo"=gam.lat.lo,
      "laty.up"=gam.lat.up,
      "yearx"=gam.year.grid$year,
      "yeary"=gam.year.fit,
      "yeary.lo"=gam.year.lo,
      "yeary.up"=gam.year.up
    )
    write.table(GAMmodDBinD.dat, "GAMmodDBinD.csv", sep=",", row.names = F)
    print(c(summary(gam.fit)$r.sq, summary(gam.fit)$dev.expl))
    
    
    ####################################
    ## remove arid and semi-arid points
    ## rainfall data
    ## https://ausenv.tern.org.au/aer/how-to-use-australias-environment-data-explorer/aer/australias-environment/index.html
    ## https://thredds.nci.org.au/thredds/catalog/ub8/au/OzWALD/annual/catalog.html
    
    setwd("~/Documents/GitHub/AusIndigN/data")
    rain <- nc_open("OzWALD.annual.Pg.AnnualSums.nc")
    print(rain)
    rain.dat <- ncvar_get(rain, "AnnualSums")
    lon.rain <- ncvar_get(rain, "longitude")
    lat.rain <- ncvar_get(rain, "latitude")
    
    rain.rst <- rast(rain.dat)
    ext(rain.rst) <- ext(min(lon.rain), max(lon.rain), min(lat.rain, na.rm=T), max(lat.rain, na.rm=T))
    crs(rain.rst) <- "epsg:4326"  # set the coordinate reference system (typically WGS84)
    nc_close(rain)
    terra::plot(rain.rst)
    rain.rst
    rain.mn.rst <- app(rain.rst, fun = mean, na.rm = T)
    terra::plot(rain.mn.rst)
    
    ## overlay bindensModOverl points on rain.mn.rst
    bindensModOverl.coords <- bindensModOverl[, c("lon", "lat")]
    rownames(bindensModOverl.coords) <- bindensModOverl$GN
    bindensModOverl.pts <- vect(bindensModOverl.coords, crs = crs(rain.mn.rst))
    terra::plot(rain.mn.rst)
    plot(bindensModOverl.pts, add = TRUE, col = "red", pch = 19)
    
    # extract
    head(bindensModOverl)
    bindensModOverlrain <- terra::extract(rain.mn.rst, bindensModOverl.coords, method = "bilinear", search_radius = 20000)
    head(bindensModOverlrain)
    
    # add to data
    head(bindensModOverl)
    bindensModOverl$rain <- bindensModOverlrain$mean
    head(bindensModOverl)
    
    ## which points have no rainfall?
    bindensModOverl[which(is.na(bindensModOverl$rain) == T),]
    
    ## which points have rainfall ≤ 250 mm/year (arid), and which have > 250 mm/year but ≤ 350 mm/year (semi-arid)?
    bindensModOverl$arid <- ifelse(bindensModOverl$rain <= 250, 1, 0)
    bindensModOverl$semi.arid <- ifelse(bindensModOverl$rain > 250 & bindensModOverl$rain <= 370, 1, 0)
    bindensModOverl$ar.sabin <- ifelse(bindensModOverl$arid == 1 | bindensModOverl$semi.arid == 1, 1, 0)
    
    ## only take non-arid/non-semi-arid points
    bindensModOverl.wet <- bindensModOverl[bindensModOverl$ar.sabin == 0, ]
    head(bindensModOverl.wet)
    dim(bindensModOverl.wet)
    dim(bindensModOverl)
    
    sum(bindensModOverl$ar.sabin)
    sum(bindensModOverl$arid)
    sum(bindensModOverl$semi.arid)
    
    ## save to .csv
    setwd("/Users/brad0317/Documents/GitHub/AusIndigN/out")
    write.table(bindensModOverl.wet, "bindensModOverl.wet.csv", sep=",", row.names = F)
    write.table(bindensModOverl, "bindensModOverl.csv", sep=",", row.names = F)
    
    
    brt.fit.wet <- gbm.step(bindensModOverl.wet, gbm.x = attr(bindensModOverl.wet, "names")[c(2,4)],
                        gbm.y = attr(bindensModOverl.wet, "names")[11], 
                        family="gaussian", max.trees=100000, tolerance = 0.0002, learning.rate = 0.00025, 
                        bag.fraction=0.75, tree.complexity = 2)
    summary(brt.fit.wet)
    gbmpl <- gbm.plot(brt.fit.wet, smooth=T, n.plots=2, common.scale=T, y.label="log10 model D:Binford D", plot.layout = c(1,2),
                      show.contrib = T, rug=T)
    gbm.plot.fits(brt.fit.wet)
    brt.fit.wet$fitted.vars
    
    par(mfrow=c(1,2))
    x2.wet <- plot.gbm(brt.fit.wet, i.var=brt.fit.wet$var.names[2], continuous.resolution=100, return.grid=T)[,1]
    y2.wet <- 10^plot.gbm(brt.fit.wet, i.var=brt.fit.wet$var.names[2], continuous.resolution=100, return.grid=T)[,2]
    plot(x2.wet,y2.wet,type="l", xlab=brt.fit.wet$var.names[2], ylab="model D:Binford D", ylim=c(0,9))
    x1.wet <- plot.gbm(brt.fit.wet, i.var=brt.fit.wet$var.names[1], continuous.resolution=100, return.grid=T)[,1]
    y1.wet <- 10^plot.gbm(brt.fit.wet, i.var=brt.fit.wet$var.names[1], continuous.resolution=100, return.grid=T)[,2]
    plot(x1.wet,y1.wet,type="l", xlab=brt.fit.wet$var.names[1], ylab="model D:Binford D", ylim=c(0,9))
    par(mfrow=c(1,1))
    
    BRTmodDBinDwet.dat <- data.frame("latx"=x2.wet, "laty"=y2.wet, "yearx"=x1.wet, "yeary"=y1.wet)
    write.table(BRTmodDBinDwet.dat, "BRTmodDBinDwet.csv", sep=",", row.names = F)
    
    CV.cor.wet <- fitted.varsCV.cor.wet <- 100 * brt.fit.wet$cv.statistics$correlation.mean
    CV.cor.se.wet <- 100 * brt.fit.wet$cv.statistics$correlation.se
    print(c(CV.cor.wet, CV.cor.se.wet))
    
    # GAM analogue after removing arid and semi-arid points
    gam.fit.wet <- mgcv::gam(
      DratioM2B.sc ~
        s(year, k = 10) +
        s(lat, k = 10),
      data = bindensModOverl.wet,
      family = gaussian(),
      method = "REML"
    )
    summary(gam.fit.wet)
    mgcv::gam.check(gam.fit.wet)
    
    mean.year.wet <- mean(bindensModOverl.wet$year, na.rm=T)
    mean.lat.wet <- mean(bindensModOverl.wet$lat, na.rm=T)
    
    gam.year.grid.wet <- data.frame(
      year = seq(min(bindensModOverl.wet$year, na.rm=T), max(bindensModOverl.wet$year, na.rm=T), length.out=100),
      lat = mean.lat.wet
    )
    gam.lat.grid.wet <- data.frame(
      year = mean.year.wet,
      lat = seq(min(bindensModOverl.wet$lat, na.rm=T), max(bindensModOverl.wet$lat, na.rm=T), length.out=100)
    )
    
    gam.year.pred.wet <- predict(gam.fit.wet, newdata = gam.year.grid.wet, type = "response", se.fit = TRUE)
    gam.lat.pred.wet <- predict(gam.fit.wet, newdata = gam.lat.grid.wet, type = "response", se.fit = TRUE)
    
    gam.year.fit.wet <- back.transform.Dratio(as.numeric(gam.year.pred.wet$fit))
    gam.year.lo.wet <- back.transform.Dratio(as.numeric(gam.year.pred.wet$fit - 1.96 * gam.year.pred.wet$se.fit))
    gam.year.up.wet <- back.transform.Dratio(as.numeric(gam.year.pred.wet$fit + 1.96 * gam.year.pred.wet$se.fit))
    
    gam.lat.fit.wet <- back.transform.Dratio(as.numeric(gam.lat.pred.wet$fit))
    gam.lat.lo.wet <- back.transform.Dratio(as.numeric(gam.lat.pred.wet$fit - 1.96 * gam.lat.pred.wet$se.fit))
    gam.lat.up.wet <- back.transform.Dratio(as.numeric(gam.lat.pred.wet$fit + 1.96 * gam.lat.pred.wet$se.fit))
    
    par(mfrow=c(1,2))
    plot(gam.lat.grid.wet$lat, gam.lat.fit.wet, type="l", xlab="lat", ylab="model D:Binford D",
         ylim=c(min(gam.lat.lo.wet, na.rm=T), max(gam.lat.up.wet, na.rm=T)))
    lines(gam.lat.grid.wet$lat, gam.lat.lo.wet, lty=2, col="red")
    lines(gam.lat.grid.wet$lat, gam.lat.up.wet, lty=2, col="red")
    plot(gam.year.grid.wet$year, gam.year.fit.wet, type="l", xlab="year", ylab="model D:Binford D",
         ylim=c(min(gam.year.lo.wet, na.rm=T), max(gam.year.up.wet, na.rm=T)))
    lines(gam.year.grid.wet$year, gam.year.lo.wet, lty=2, col="red")
    lines(gam.year.grid.wet$year, gam.year.up.wet, lty=2, col="red")
    par(mfrow=c(1,1))
    
    GAMmodDBinDwet.dat <- data.frame(
      "latx"=gam.lat.grid.wet$lat,
      "laty"=gam.lat.fit.wet,
      "laty.lo"=gam.lat.lo.wet,
      "laty.up"=gam.lat.up.wet,
      "yearx"=gam.year.grid.wet$year,
      "yeary"=gam.year.fit.wet,
      "yeary.lo"=gam.year.lo.wet,
      "yeary.up"=gam.year.up.wet
    )
    write.table(GAMmodDBinDwet.dat, "GAMmodDBinDwet.csv", sep=",", row.names = F)
    print(c(summary(gam.fit.wet)$r.sq, summary(gam.fit.wet)$dev.expl))
    
    
    
    
    ## add stochastic spatial resampling procedure to reduce impact of spatial autocorrelation
    ## ensure that no two points are within the minimum thinning distance in each resampled dataset;
    ## repeat 100 times; fit BRT to each resampled dataset;
    ## extract variable importance and partial dependence plots for each resampled dataset;
    ## calculate mean and SE of variable importance and partial dependence across resampled dataset

    moran_corr <- function(y, dist_mat, breaks, nsim = 199L, min_pairs = 10L, min_nodes = 8L) {
      results <- data.frame(
        lag_mid = (breaks[-length(breaks)] + breaks[-1]) / 2,
        moran_I = NA_real_,
        p_value = NA_real_,
        n_pairs = NA_integer_,
        n_nodes = NA_integer_
      )
      for (i in seq_len(nrow(results))) {
        lo    <- breaks[i];   hi <- breaks[i + 1]
        w_mat <- ((dist_mat > lo) & (dist_mat <= hi)) * 1L
        diag(w_mat) <- 0L
        results$n_pairs[i] <- sum(w_mat) / 2L
        if (results$n_pairs[i] < min_pairs) next
        w_list <- spdep::mat2listw(w_mat, style = "B", zero.policy = TRUE)
        results$n_nodes[i] <- sum(spdep::card(w_list$neighbours) > 0L)
        if (results$n_nodes[i] < min_nodes) next
        mt     <- tryCatch(
          spdep::moran.mc(y, w_list, nsim = nsim, zero.policy = TRUE, alternative = "two.sided"),
          error = function(e) NULL
        )
        if (!is.null(mt)) {
          results$moran_I[i] <- unname(mt$statistic)
          results$p_value[i] <- mt$p.value
        }
      }
      results
    }
    n.resamp   <- 100
    pd.grid.n  <- 100    # resolution for partial dependence grids
    n.min      <- 10     # minimum thinned obs to attempt BRT

    # -----------------------------------------------------------
    # gbm.step does not forward n.minobsinnode to its internal gbm()
    # calls (it builds them as pasted strings). Patch the body to
    # inject the parameter so small thinned datasets don't trigger
    # the "nTrain * bag.fraction <= 2 * n.minobsinnode + 1" error.
    # -----------------------------------------------------------
    gbm.step.patched <- gbm.step
    body_lines <- deparse(body(gbm.step), width.cutoff = 500)
    body_lines <- gsub("verbose = FALSE\\)",
                       "verbose = FALSE, n.minobsinnode = n.minobsinnode)",
                       body_lines)
    formals(gbm.step.patched)$n.minobsinnode <- 10L
    body(gbm.step.patched) <- parse(text = paste(body_lines, collapse = "\n"))

    # -----------------------------------------------------------
    # greedy random spatial thinning: shuffle, then keep points
    # that are >= min.dist km from all previously kept points
    # -----------------------------------------------------------
    spatial_thin <- function(data, coords, min.dist) {
      idx <- sample(nrow(data))
      kept <- idx[1]
      for (i in idx[-1]) {
        d <- sp::spDistsN1(coords[kept, , drop = FALSE], coords[i, ], longlat = TRUE)
        if (all(d >= min.dist)) kept <- c(kept, i)
      }
      data[kept, ]
    }
    
    # fixed x-grids from full-data range (so PD curves are on a common axis)
    # pd.xgrid <- setNames(
    #   lapply(brt.fit$var.names, function(v) {
    #     r <- range(bindensModOverl[[v]], na.rm = TRUE)
    #     seq(r[1], r[2], length.out = pd.grid.n)
    #   }),
    #   brt.fit$var.names
    # )
    
    pd.xgrid <- setNames(
      lapply(brt.fit.wet$var.names, function(v) {
        r <- range(bindensModOverl.wet[[v]], na.rm = TRUE)
        seq(r[1], r[2], length.out = pd.grid.n)
      }),
      brt.fit.wet$var.names
    )
    gam.var.names <- c("year", "lat")
    gam.xgrid <- setNames(
      lapply(gam.var.names, function(v) {
        r <- range(bindensModOverl.wet[[v]], na.rm = TRUE)
        seq(r[1], r[2], length.out = pd.grid.n)
      }),
      gam.var.names
    )
    
    # storage
    var.imp.mat <- matrix(NA, n.resamp, length(brt.fit.wet$var.names),
                          dimnames = list(NULL, brt.fit.wet$var.names))
    
    pd.list <- setNames(
     lapply(brt.fit.wet$var.names, function(v) matrix(NA, n.resamp, pd.grid.n)),
     brt.fit.wet$var.names
    )
    gam.pd.list <- setNames(
      lapply(gam.var.names, function(v) matrix(NA, n.resamp, pd.grid.n)),
      gam.var.names
    )
    n.obs.vec <- integer(n.resamp)
    
    # -----------------------------------------------------------
    # adaptive BRT: iterates lr large→small, stopping at the
    # first value that places n.trees in [target.min, max.trees*0.9]
    # (largest lr in target range = fewest trees = max efficiency).
    # step.size, tolerance, and n.minobsinnode are scaled to dataset size.
    # Uses gbm.step.patched to forward n.minobsinnode correctly.
    # -----------------------------------------------------------
    adaptive_brt <- function(dat, gbm.x, gbm.y,
                             tree.complexity, bag.fraction,
                             n.folds         = NULL,
                             max.trees       = 8000,
                             target.min      = 300,
                             lr.candidates   = c(0.05, 0.02, 0.01)) {
      n         <- nrow(dat)
      if (is.null(n.folds)) {
        n.folds <- max(3L, min(5L, floor(n / 4L)))
      }
      # larger step.size for larger n: coarser CV steps, faster convergence
      step.size <- max(5L, round(n / 2L))
      # loosen tolerance for small n where CV loss is noisier
      tolerance <- 0.002 * sqrt(30 / n)
      # scale n.minobsinnode to satisfy: nTrain * bag.fraction > 2 * n.minobsinnode + 1
      n.train   <- floor(n * (n.folds - 1L) / n.folds)
      n.minobs  <- max(2L, floor((n.train * bag.fraction - 2) / 2) - 1L)

      best.fit   <- NULL
      params.log <- NULL

      for (lr in lr.candidates) {
        fit_try <- tryCatch(
          suppressMessages(suppressWarnings(
            gbm.step.patched(dat,
                             gbm.x           = gbm.x,
                             gbm.y           = gbm.y,
                             family          = "gaussian",
                             max.trees       = max.trees,
                             tolerance       = tolerance,
                             learning.rate   = lr,
                             bag.fraction    = bag.fraction,
                             tree.complexity = tree.complexity,
                             step.size       = step.size,
                             n.folds         = n.folds,
                             n.minobsinnode  = n.minobs,
                             silent          = TRUE,
                             plot.main       = FALSE)
          )),
          error = function(e) NULL
        )
        
        if (is.null(fit_try) || is.null(fit_try$n.trees)) next

        nt <- fit_try$n.trees
        if (!is.finite(nt) || length(nt) != 1L) next
        
        best.fit   <- fit_try
        params.log <- list(lr             = lr,
                           n.folds        = n.folds,
                           step.size      = step.size,
                           tolerance      = round(tolerance, 6),
                           n.minobsinnode = n.minobs,
                           n.trees        = nt)
        # accept: enough trees and didn't hit the ceiling
        if (nt >= target.min && nt < max.trees * 0.9) break
      }

      list(fit = best.fit, params = params.log)
    }
    
    gam_pd_curve <- function(fit, xgrid, focal_var, year_fixed, lat_fixed) {
      newdat <- data.frame(
        year = rep(year_fixed, length(xgrid)),
        lat = rep(lat_fixed, length(xgrid))
      )
      newdat[[focal_var]] <- xgrid
      as.numeric(predict(fit, newdata = newdat, type = "response"))
    }
    
    adaptive_gam <- function(dat, k.max = 10L) {
      year_unique <- length(unique(dat$year))
      lat_unique <- length(unique(dat$lat))
      if (year_unique < 4L || lat_unique < 4L) return(NULL)
      
      k.year <- min(k.max, year_unique - 1L)
      k.lat <- min(k.max, lat_unique - 1L)
      
      tryCatch(
        suppressWarnings(
          mgcv::gam(
            DratioM2B.sc ~
              s(year, k = k.year) +
              s(lat, k = k.lat),
            data = dat,
            family = gaussian(),
            method = "REML"
          )
        ),
        error = function(e) NULL
      )
    }

    sc_scale  <- attr(bindensModOverl$DratioM2B.sc, "scaled:scale")
    sc_center <- attr(bindensModOverl$DratioM2B.sc, "scaled:center")
    out_dir <- "/Users/brad0317/Documents/GitHub/AusIndigN/out/"
    
    # back-transform helper: standardised PD → original DratioM2B units
    bt <- function(x) x * sc_scale + sc_center
    
    pd_summary_df <- function(pd.lst, pd.xgrid, var.names, label) {
      do.call(rbind, lapply(var.names, function(v) {
        m <- pd.lst[[v]]
        data.frame(
          variable = v,
          run      = label,
          x        = pd.xgrid[[v]],
          mean.y   = bt(colMeans(m, na.rm = TRUE)),
          se.y     = apply(m, 2, function(col) sd(col, na.rm=TRUE) / sqrt(sum(!is.na(col)))) * sc_scale
        )
      }))
    }

    gam_relative_contrib <- function(fit, dat) {
      term_mat <- tryCatch(
        predict(fit, newdata = dat, type = "terms"),
        error = function(e) NULL
      )
      if (is.null(term_mat)) {
        return(c(year = NA_real_, lat = NA_real_))
      }
      term_mat <- as.matrix(term_mat)
      term_names <- gsub(" ", "", colnames(term_mat))
      year_idx <- grepl("^s\\(year\\)", term_names)
      lat_idx <- grepl("^s\\(lat\\)", term_names)
      var_year <- if (any(year_idx)) stats::var(rowSums(term_mat[, year_idx, drop = FALSE]), na.rm = TRUE) else 0
      var_lat <- if (any(lat_idx)) stats::var(rowSums(term_mat[, lat_idx, drop = FALSE]), na.rm = TRUE) else 0
      total_var <- sum(c(var_year, var_lat), na.rm = TRUE)
      if (!is.finite(total_var) || total_var <= 0) {
        return(c(year = NA_real_, lat = NA_real_))
      }
      100 * c(
        year = var_year / total_var,
        lat = var_lat / total_var
      )
    }

    derive_min_dist <- function(mc_raw) {
      valid <- mc_raw[is.finite(mc_raw$lag_mid) &
                        is.finite(mc_raw$moran_I) &
                        is.finite(mc_raw$p_value), ]
      
      sig_pos <- valid[valid$p_value < 0.05 & valid$moran_I > 0, ]
      if (nrow(sig_pos) > 0) {
        return(min(sig_pos$lag_mid))
      }
      
      pos <- valid[valid$moran_I > 0, ]
      if (nrow(pos) > 0) {
        return(pos$lag_mid[which.max(pos$moran_I)])
      }
      
      if (nrow(valid) > 0) {
        return(valid$lag_mid[which.max(valid$n_pairs)])
      }
      
      mean(range(mc_raw$lag_mid, na.rm = TRUE))
    }

    run_resampling_suite <- function(dat, coords, brt_fit, gam_fit,
                                     mean_year_use, mean_lat_use,
                                     dataset_key, dataset_label) {
      dist_mat <- sp::spDists(coords, longlat = TRUE)
      y_raw <- as.numeric(scale(dat$DratioM2B.sc))
      y_resid <- as.numeric(
        scale(as.numeric(dat$DratioM2B.sc) -
                predict(brt_fit, dat, n.trees = brt_fit$n.trees))
      )
      
      moran.breaks <- seq(0, 2000, by = 100)
      mc_raw <- moran_corr(y_raw, dist_mat, moran.breaks)
      mc_resid <- moran_corr(y_resid, dist_mat, moran.breaks)
      min.dist <- derive_min_dist(mc_raw)
      resample_label <- paste0(min.dist, " km (resampled)")
      dist_tag <- paste0(min.dist, "km")
      
      cat("\n", dataset_label, " Moran's I correlogram – calculated thinning distance:", min.dist, "km\n", sep = "")
      cat("setting min.dist =", min.dist, "km for spatial thinning\n\n")
      
      mc_raw$series <- "raw response"
      mc_resid$series <- "BRT residuals"
      mc_plot <- rbind(mc_raw, mc_resid)
      mc_plot <- mc_plot[!is.na(mc_plot$n_pairs) & mc_plot$n_pairs > 0, ]
      mc_plot$sig <- ifelse(mc_plot$p_value < 0.05, "p < 0.05", "p \u2265 0.05")
      
      moran_plot <- ggplot(mc_plot, aes(x = lag_mid, y = moran_I)) +
        geom_hline(yintercept = 0, linetype = "dashed", colour = "grey60") +
        geom_vline(xintercept = min.dist, linetype = "dotted",
                   colour = "steelblue", linewidth = 0.7) +
        geom_line(colour = "grey70") +
        geom_point(aes(fill = sig), shape = 21, size = 3) +
        scale_fill_manual(values = c("p < 0.05" = "#d73027", "p \u2265 0.05" = "white"),
                          name = NULL) +
        scale_x_continuous(breaks = seq(0, 2000, 200)) +
        facet_wrap(~series, ncol = 1) +
        labs(x = "distance lag (km)", y = "Moran's I",
             title = paste("Moran's I correlogram:", dataset_label),
             subtitle = paste0("dotted line = min.dist (", min.dist, " km)")) +
        theme_bw(base_size = 12) +
        theme(legend.position = "bottom")
      print(moran_plot)
      
      pd.xgrid <- setNames(
        lapply(brt_fit$var.names, function(v) {
          r <- range(dat[[v]], na.rm = TRUE)
          seq(r[1], r[2], length.out = pd.grid.n)
        }),
        brt_fit$var.names
      )
      gam.xgrid <- setNames(
        lapply(gam.var.names, function(v) {
          r <- range(dat[[v]], na.rm = TRUE)
          seq(r[1], r[2], length.out = pd.grid.n)
        }),
        gam.var.names
      )
      
      var.imp.mat <- matrix(NA, n.resamp, length(brt_fit$var.names),
                            dimnames = list(NULL, brt_fit$var.names))
      pd.list <- setNames(
        lapply(brt_fit$var.names, function(v) matrix(NA, n.resamp, pd.grid.n)),
        brt_fit$var.names
      )
      gam.pd.list <- setNames(
        lapply(gam.var.names, function(v) matrix(NA, n.resamp, pd.grid.n)),
        gam.var.names
      )
      n.obs.vec <- integer(n.resamp)
      params.log.list <- vector("list", n.resamp)
      cv.cor.vec <- rep(NA_real_, n.resamp)
      cv.cor.se.vec <- rep(NA_real_, n.resamp)
      cv.dev.vec <- rep(NA_real_, n.resamp)
      cv.dev.se.vec <- rep(NA_real_, n.resamp)
      gam.r.sq.vec <- rep(NA_real_, n.resamp)
      gam.dev.expl.vec <- rep(NA_real_, n.resamp)
      gam.year.rel.vec <- rep(NA_real_, n.resamp)
      gam.lat.rel.vec <- rep(NA_real_, n.resamp)
      iter.elapsed.vec <- rep(NA_real_, n.resamp)
      
      cat("Starting", dataset_label, "resampling loop\n")
      set.seed(7421)
      pb <- txtProgressBar(min = 0, max = n.resamp, style = 3)
      
      for (iter in seq_len(n.resamp)) {
        iter.start <- proc.time()[3]
        thin_dat <- spatial_thin(dat, coords, min.dist)
        n.obs.vec[iter] <- nrow(thin_dat)
        
        if (nrow(thin_dat) < n.min) {
          iter.elapsed.vec[iter] <- proc.time()[3] - iter.start
          setTxtProgressBar(pb, iter)
          next
        }
        
        res_iter <- adaptive_brt(thin_dat,
                                 gbm.x = match(brt_fit$var.names, names(thin_dat)),
                                 gbm.y = match("DratioM2B.sc", names(thin_dat)),
                                 tree.complexity = 2,
                                 bag.fraction = 0.75)
        fit_iter <- res_iter$fit
        params.log.list[[iter]] <- res_iter$params
        gam.fit.iter <- adaptive_gam(thin_dat)
        
        if (!is.null(fit_iter)) {
          vi <- summary(fit_iter, plotit = FALSE)
          var.imp.mat[iter, vi$var] <- vi$rel.inf
          
          for (v in brt_fit$var.names) {
            pd <- plot.gbm(fit_iter, i.var = v,
                           continuous.resolution = pd.grid.n, return.grid = TRUE)
            pd.list[[v]][iter, ] <- approx(pd[, 1], pd[, 2],
                                           xout = pd.xgrid[[v]], rule = 2)$y
          }
          
          cv.cor.vec[iter] <- fit_iter$cv.statistics$correlation.mean
          cv.cor.se.vec[iter] <- fit_iter$cv.statistics$correlation.se
          cv.dev.vec[iter] <- fit_iter$cv.statistics$deviance.mean
          cv.dev.se.vec[iter] <- fit_iter$cv.statistics$deviance.se
        }
        
        if (!is.null(gam.fit.iter)) {
          gam.summ <- summary(gam.fit.iter)
          gam.contrib <- gam_relative_contrib(gam.fit.iter, thin_dat)
          gam.r.sq.vec[iter] <- gam.summ$r.sq
          gam.dev.expl.vec[iter] <- gam.summ$dev.expl
          gam.year.rel.vec[iter] <- gam.contrib["year"]
          gam.lat.rel.vec[iter] <- gam.contrib["lat"]
          
          for (v in gam.var.names) {
            gam.pd.list[[v]][iter, ] <- gam_pd_curve(
              fit = gam.fit.iter,
              xgrid = gam.xgrid[[v]],
              focal_var = v,
              year_fixed = mean_year_use,
              lat_fixed = mean_lat_use
            )
          }
        }
        
        iter.elapsed.vec[iter] <- proc.time()[3] - iter.start
        if (iter %% 10 == 0) {
          p <- params.log.list[[iter]]
          if (!is.null(p) && !is.null(gam.fit.iter)) {
            cat(sprintf("%s resample %3d / %d | n = %2d | lr = %.4f | folds = %d | trees = %d | iter.sec = %.2f | CV.cor = %.3f | GAM R2 = %.3f | year = %.1f%% | lat = %.1f%%\n",
                        dataset_label, iter, n.resamp, nrow(thin_dat), p$lr, p$n.folds, p$n.trees,
                        iter.elapsed.vec[iter], cv.cor.vec[iter], gam.r.sq.vec[iter],
                        gam.year.rel.vec[iter], gam.lat.rel.vec[iter]))
          } else {
            cat(sprintf("%s resample %3d / %d | n = %2d | iter.sec = %.2f | fit failed\n",
                        dataset_label, iter, n.resamp, nrow(thin_dat), iter.elapsed.vec[iter]))
          }
        }
        setTxtProgressBar(pb, iter)
      }
      close(pb)
      
      cat("\n", dataset_label, " resampling done.\n", sep = "")
      cat("obs per resample  – mean:", round(mean(n.obs.vec), 1),
          " range:", range(n.obs.vec)[1], "-", range(n.obs.vec)[2], "\n")
      cat("valid BRT fits    :", sum(!is.na(var.imp.mat[, 1])), "/", n.resamp, "\n")
      cat("valid GAM fits    :", sum(!is.na(gam.r.sq.vec)), "/", n.resamp, "\n")
      
      params.df <- do.call(rbind, lapply(seq_len(n.resamp), function(r) {
        p <- params.log.list[[r]]
        if (is.null(p)) return(data.frame(resamp = r,
                                          n.obs = n.obs.vec[r],
                                          lr = NA, n.folds = NA, step.size = NA,
                                          tolerance = NA, n.trees = NA,
                                          cv.cor = NA, cv.cor.se = NA,
                                          cv.dev = NA, cv.dev.se = NA,
                                          iter.sec = iter.elapsed.vec[r]))
        data.frame(resamp = r,
                   n.obs = n.obs.vec[r],
                   lr = p$lr,
                   n.folds = p$n.folds,
                   step.size = p$step.size,
                   tolerance = p$tolerance,
                   n.trees = p$n.trees,
                   cv.cor = cv.cor.vec[r],
                   cv.cor.se = cv.cor.se.vec[r],
                   cv.dev = cv.dev.vec[r],
                   cv.dev.se = cv.dev.se.vec[r],
                   iter.sec = iter.elapsed.vec[r])
      }))
      gam_resample_stats <- data.frame(
        resamp = seq_len(n.resamp),
        n.obs = n.obs.vec,
        r.sq = gam.r.sq.vec,
        dev.expl = gam.dev.expl.vec,
        year_rel_contribution = gam.year.rel.vec,
        lat_rel_contribution = gam.lat.rel.vec,
        iter.sec = iter.elapsed.vec
      )
      gam_full_contrib <- data.frame(
        dataset = dataset_key,
        year_rel_contribution = gam_relative_contrib(gam_fit, dat)["year"],
        lat_rel_contribution = gam_relative_contrib(gam_fit, dat)["lat"]
      )
      vi.mean <- colMeans(var.imp.mat, na.rm = TRUE)
      vi.se <- apply(var.imp.mat, 2, function(x) sd(x, na.rm = TRUE) / sqrt(sum(!is.na(x))))
      vi.summary <- data.frame(variable = names(vi.mean),
                               mean.rel.inf = vi.mean,
                               se.rel.inf = vi.se)
      
      brt_resampled <- pd_summary_df(pd.list, pd.xgrid, brt_fit$var.names, resample_label)
      gam_resampled <- pd_summary_df(gam.pd.list, gam.xgrid, gam.var.names, resample_label)
      
      brt_orig <- do.call(rbind, lapply(brt_fit$var.names, function(v) {
        raw <- plot.gbm(brt_fit, i.var = v, continuous.resolution = 200, return.grid = TRUE)
        data.frame(
          variable = v,
          run = "full-data BRT",
          x = pd.xgrid[[v]],
          mean.y = bt(approx(raw[, 1], raw[, 2], xout = pd.xgrid[[v]], rule = 2)$y),
          se.y = 0
        )
      }))
      brt_pd_all <- rbind(brt_resampled, brt_orig)
      brt_pd_all$run <- factor(brt_pd_all$run,
                               levels = c("full-data BRT", resample_label))
      brt_pd_all$var_label <- ifelse(brt_pd_all$variable == "year", "Year", "Latitude (°)")
      
      gam_orig <- do.call(rbind, lapply(gam.var.names, function(v) {
        data.frame(
          variable = v,
          run = "full-data GAM",
          x = gam.xgrid[[v]],
          mean.y = bt(gam_pd_curve(
            fit = gam_fit,
            xgrid = gam.xgrid[[v]],
            focal_var = v,
            year_fixed = mean_year_use,
            lat_fixed = mean_lat_use
          )),
          se.y = 0
        )
      }))
      gam_pd_all <- rbind(gam_resampled, gam_orig)
      gam_pd_all$run <- factor(gam_pd_all$run,
                               levels = c("full-data GAM", resample_label))
      gam_pd_all$var_label <- ifelse(gam_pd_all$variable == "year", "Year", "Latitude (°)")
      
      brt_plot <- ggplot(brt_pd_all, aes(x = x, y = mean.y, colour = run, fill = run)) +
        geom_ribbon(data = subset(brt_pd_all, run != "full-data BRT"),
                    aes(ymin = mean.y - se.y, ymax = mean.y + se.y),
                    alpha = 0.15, colour = NA) +
        geom_line(aes(linewidth = run == "full-data BRT")) +
        scale_linewidth_manual(values = c(`TRUE` = 1.1, `FALSE` = 0.75), guide = "none") +
        scale_colour_manual(values = c("full-data BRT" = "black",
                                       stats::setNames("#e07b54", resample_label)),
                            name = NULL) +
        scale_fill_manual(values = c("full-data BRT" = NA,
                                     stats::setNames("#e07b54", resample_label)),
                          name = NULL) +
        facet_wrap(~var_label, scales = "free_x", ncol = 2) +
        labs(x = NULL,
             y = expression(paste("model:Binford population density ratio (", italic(D)[ratio], ")")),
             title = paste("BRT partial dependence:", dataset_label, "full-data vs. spatially resampled fits")) +
        theme_bw(base_size = 12) +
        theme(legend.position = "bottom",
              strip.text = element_text(face = "bold"))
      
      gam_plot <- ggplot(gam_pd_all, aes(x = x, y = mean.y, colour = run, fill = run)) +
        geom_ribbon(data = subset(gam_pd_all, run != "full-data GAM"),
                    aes(ymin = mean.y - se.y, ymax = mean.y + se.y),
                    alpha = 0.15, colour = NA) +
        geom_line(aes(linewidth = run == "full-data GAM")) +
        scale_linewidth_manual(values = c(`TRUE` = 1.1, `FALSE` = 0.75), guide = "none") +
        scale_colour_manual(values = c("full-data GAM" = "black",
                                       stats::setNames("#4e9ac7", resample_label)),
                            name = NULL) +
        scale_fill_manual(values = c("full-data GAM" = NA,
                                     stats::setNames("#4e9ac7", resample_label)),
                          name = NULL) +
        facet_wrap(~var_label, scales = "free_x", ncol = 2) +
        labs(x = NULL,
             y = expression(paste("model:Binford population density ratio (", italic(D)[ratio], ")")),
             title = paste("GAM partial dependence:", dataset_label, "full-data vs. spatially resampled fits")) +
        theme_bw(base_size = 12) +
        theme(legend.position = "bottom",
              strip.text = element_text(face = "bold"))
      
      print(brt_plot)
      print(gam_plot)
      
      write.csv(brt_pd_all,
                file = file.path(out_dir, paste0("BRT_pd_", dataset_key, "_all.csv")),
                row.names = FALSE)
      write.csv(brt_resampled,
                file = file.path(out_dir, paste0("BRT_pd_", dataset_key, "_", dist_tag, ".csv")),
                row.names = FALSE)
      write.csv(params.df,
                file = file.path(out_dir, paste0("BRT_resample_stats_", dataset_key, ".csv")),
                row.names = FALSE)
      write.csv(vi.summary,
                file = file.path(out_dir, paste0("BRT_varimp_", dataset_key, ".csv")),
                row.names = FALSE)
      write.csv(gam_pd_all,
                file = file.path(out_dir, paste0("GAM_pd_", dataset_key, "_all.csv")),
                row.names = FALSE)
      write.csv(gam_resampled,
                file = file.path(out_dir, paste0("GAM_pd_", dataset_key, "_", dist_tag, ".csv")),
                row.names = FALSE)
      write.csv(gam_resample_stats,
                file = file.path(out_dir, paste0("GAM_resample_stats_", dataset_key, ".csv")),
                row.names = FALSE)
      write.csv(gam_full_contrib,
                file = file.path(out_dir, paste0("GAM_full_contrib_", dataset_key, ".csv")),
                row.names = FALSE)
      ggsave(filename = file.path(out_dir, paste0("Moran_", dataset_key, ".png")),
             plot = moran_plot, width = 8, height = 8, dpi = 300)
      ggsave(filename = file.path(out_dir, paste0("BRT_pd_", dataset_key, ".png")),
             plot = brt_plot, width = 10, height = 6, dpi = 300)
      ggsave(filename = file.path(out_dir, paste0("GAM_pd_", dataset_key, ".png")),
             plot = gam_plot, width = 10, height = 6, dpi = 300)
      
      cat("written ", dataset_label, " outputs:\n", sep = "")
      cat(" ", file.path(out_dir, paste0("BRT_pd_", dataset_key, "_all.csv")), "—", nrow(brt_pd_all), "rows\n")
      cat(" ", file.path(out_dir, paste0("GAM_pd_", dataset_key, "_all.csv")), "—", nrow(gam_pd_all), "rows\n")
      cat(" ", file.path(out_dir, paste0("GAM_resample_stats_", dataset_key, ".csv")), "—", nrow(gam_resample_stats), "rows\n")
      cat(" ", file.path(out_dir, paste0("GAM_full_contrib_", dataset_key, ".csv")), "\n")
      cat(" ", file.path(out_dir, paste0("BRT_pd_", dataset_key, ".png")), "\n")
      cat(" ", file.path(out_dir, paste0("GAM_pd_", dataset_key, ".png")), "\n")
    }
    
    coords.all <- as.matrix(bindensModOverl[, c("lon", "lat")])
    coords.wet <- as.matrix(bindensModOverl.wet[, c("lon", "lat")])
    
    run_resampling_suite(
      dat = bindensModOverl,
      coords = coords.all,
      brt_fit = brt.fit,
      gam_fit = gam.fit,
      mean_year_use = mean.year,
      mean_lat_use = mean.lat,
      dataset_key = "allpts",
      dataset_label = "all points"
    )
    
    run_resampling_suite(
      dat = bindensModOverl.wet,
      coords = coords.wet,
      brt_fit = brt.fit.wet,
      gam_fit = gam.fit.wet,
      mean_year_use = mean.year.wet,
      mean_lat_use = mean.lat.wet,
      dataset_key = "wet",
      dataset_label = "wet-only points"
    )
    
    # scaling parameters as a one-row lookup table
    sc_params <- data.frame(
      variable        = "DratioM2B",
      scaled.center   = sc_center,
      scaled.scale    = sc_scale,
      back_transform  = "x * scaled.scale + scaled.center"
    )
    write.csv(sc_params,
              file = file.path(out_dir, "BRT_scaling_params.csv"),
              row.names = FALSE)
    
    cat("written:\n")
    cat(" ", file.path(out_dir, "BRT_scaling_params.csv"), "— scaling parameters\n")
    
    
    
    
    
    ############################################################################################
    ## simple demographic model to estimate total mortality rate required to move from various
    ## pre-European estimates to the 1850 estimate of ~ 220 000
    ############################################################################################
    
    ## functions
    # beta distribution shape parameter estimator function
    estBetaParams <- function(mu, var) {
      alpha <- ((1 - mu) / var - 1 / mu) * mu ^ 2
      beta <- alpha * (1 / mu - 1)
      return(params = list(alpha = alpha, beta = beta))
    }

    
    # Siler hazard h(x) (Gurven et al. 2007)
    # average hunter-gatherer
    a1 <- 0.422 # initial infant mortality rate (also known as αt)
    b1 <- 1.131 # rate of mortality decline (also known as bt)
    a2 <- 0.013 # age-independent mortality (exogenous mortality due to environment); also known as ct
    a3 <- 1.47e-04 # initial adult mortality rate (also known as βt)
    b3 <- 0.086 # rate of mortality increase
    longev <- 80
    x <- seq(0,longev,1) # age vector
    h.x <- a1 * exp(-b1*x) + a2 + a3 * exp(b3 * x) # Siler's hazard model
    l.x <- exp((-a1/b1) * (1 - exp(-b1*x))) * exp(-a2 * x) * exp(a3/b3 * (1 - exp(b3 * x))) # Siler's survival (proportion surviving) model
    
    l.inf <- exp(-a1/b1) # survival at infinite time
    T.m <- 1/b1 # time constant at which maturity is approached
    h.m <- a2 # hazard for mature animals
    l.m <- exp(-a2*x) # survival
    h.s <- a3*exp(b3*x) # hazard for senescence
    l.s <- exp((a3/b3)*(1 - exp(b3*x))) # survival for senescence
    f.x <- a3*exp(b3*x)*exp((a3/b3)/(1-exp(b3*x))) # probability density function
    (log(a3) - log(a1)) / a3
    T.s <- (1/b3) # modal survival time
    
    ## survival
    init.pop <- 10000
    lx <- round(init.pop*l.x,0)
    len.lx <- length(lx)
    dx <- lx[1:(len.lx-1)]-lx[2:len.lx]
    qx <- dx/lx[1:(length(lx)-1)]
    Sx <- 1 - qx
    sx <- lx[2:len.lx]/lx[1:(len.lx-1)]
    mx <- 1 - sx
    Lx <- (lx[1:(len.lx-1)] + lx[2:len.lx])/2
    ex <- rev(cumsum(rev(Lx)))/lx[-len.lx]
    ex.avg <- ex + x[-len.lx]
    
    # set SD for Sx
    Sx.sd <- 0.05 # can set to any value
    
    # fertility (Walker et al. 2006)
    primiparity.walker <- c(17.7,18.7,19.5,18.5,18.5,18.7,25.7,19,20.5,18.8,17.8,18.6,22.2,17,16.2,18.4)
    prim.mean <- round(mean(primiparity.walker),0)
    prim.lo <- round(quantile(primiparity.walker,probs=0.025),0)
    prim.hi <- round(quantile(primiparity.walker,probs=0.975),0)
    
    setwd("/Users/brad0317/Documents/GitHub/AusIndigN/data/")
    dat.world13 <- read.table("world2013lifetable.csv", header=T, sep=",")
    fert.world13 <- dat.world13$m.f
    fert.trunc <- fert.world13[1:(longev+1)]
    pfert.trunc <- fert.trunc/sum(fert.trunc)
    fert.bentley <- 4.69/2 # Bentley 1985 for !Kung
    fert.vec <- fert.bentley * pfert.trunc
    fert.sd.vec <- 0.05*fert.vec
    
    ## construct matrix
    stages <- len.lx
    popmat <- matrix(0,nrow=stages,ncol=stages)
    colnames(popmat) <- x
    rownames(popmat) <- x
    
    ## populate matrix
    popmat[1,] <- fert.vec
    diag(popmat[2:stages,]) <- Sx
    popmat[stages,stages] <- 0 # Sx[stages-1]
    popmat.orig <- popmat ## save original matrix
    
    ## matrix properties
    max.lambda(popmat)
    r.ann <- max.r(popmat) # rate of population change, 1-yr
    #stable.stage.dist(popmat) ## stable stage distribution
    R.val(popmat,stages) # reproductive value
    gen.l <- G.val(popmat,stages) # mean generation length
    
    #stable.stage.dist(popmat) ## stable stage distribution
    R.val(popmat,stages) # reproductive value

    
    
    
    
    ## 5 million
    # initial population vector
    age.max <- 80
    pop.found <- 5000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    yr.end <- 1861 # set projection end date
    #yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # linearise model to find initial parameters for non-linear model
    lp_start <- function(K.vec, red.vec, fix.a = TRUE) {
      ok <- is.finite(K.vec) & is.finite(red.vec) & K.vec > 0 & red.vec > 0
      K <- K.vec[ok]
      r <- red.vec[ok]
      
      if (fix.a) {
        keep <- r < 1
        z <- log(1 / r[keep] - 1)
        fit0 <- lm(z ~ log(K[keep]))
        c0 <- unname(coef(fit0)[2])
        b0 <- exp(-unname(coef(fit0)[1]) / c0)
        return(c(b = b0, c = c0))
      }
      
      eps <- max(1e-4, 0.05 * diff(range(r)))
      a0 <- max(r) + eps
      z <- log(a0 / r - 1)
      fit0 <- lm(z ~ log(K))
      c0 <- max(unname(coef(fit0)[2]), 1e-3)
      b0 <- exp(-unname(coef(fit0)[1]) / c0)
      c(a = a0, b = b0, c = c0)
    }
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- lp_start(K.vec, red.vec, fix.a = TRUE)
    
    fit.lp <- nls(
      red.vec ~ 1 / (1 + (K.vec / b)^c),
      data = Kred.dat,
      algorithm = "port",
      start = as.list(param.init),
      lower = c(b = .Machine$double.eps, c = .Machine$double.eps),
      control = nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024),
      trace = TRUE
    )
    
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    #pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    pred.lp.fx <- 1/(1+(K.vec.cont/coef(fit.lp)[1])^coef(fit.lp)[2])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    #a.lp <- coef(fit.lp)[1]
    a.lp <- 1
    #b.lp <- coef(fit.lp)[2]
    b.lp <- coef(fit.lp)[1]
    #c.lp <- coef(fit.lp)[3]
    c.lp <- coef(fit.lp)[2]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]

      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo, na.rm=T),1.05*max(n.up, na.rm=T)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
   
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################

    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    killed.pyr.vec <- seq(1000, 41000, 500) # to 1861
    #killed.pyr.vec <- seq(1000, 33000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo, na.rm=T),1.05*max(n.up, na.rm=T)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end, na.rm=T), max(2*N.up.end, na.rm=T)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    #abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    #log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 4.5 million
    # initial population vector
    pop.found <- 4500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 38000, 500) # to 1861
    killed.pyr.vec <- seq(1000, 30000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    
    ## 4 million
    # initial population vector
    pop.found <- 4000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 35000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 28000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    ## 3.5 million
    # initial population vector
    pop.found <- 3500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 28000, 500) # to 1861
    killed.pyr.vec <- seq(1000, 20000, 500) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 3 million
    # initial population vector
    pop.found <- 3000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 25000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 20000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    ## 2.5 million
    # initial population vector
    pop.found <- 2500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 19000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 14000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    
    
    ## 2.22 million
    # initial population vector
    pop.found <- 2220000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 19000, 200) # to 1861
    killed.pyr.vec <- seq(1000, 14000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      ## export n.md*2
      write.csv(data.frame(year=yrs, N=n.md*2), file="NmdOut2.22M.csv", row.names=F)
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo, na.rm=T),1.05*max(n.up, na.rm=T)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end,na.rm=T), max(2*N.up.end, na.rm=T)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 2 million
    # initial population vector
    pop.found <- 2000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 16600, 200) # to 1861
    killed.pyr.vec <- seq(1000, 14000, 200) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    

    
        
    
    ## 1.5 million
    # initial population vector
    pop.found <- 1500000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 3)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 11500, 100) # to 1861
    killed.pyr.vec <- seq(1000, 8500, 100) # to 1901
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1861
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1861
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))
    
    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    
    ## 1 million
    # initial population vector
    pop.found <- 1000000 / 2
    init.vec <- stable.stage.dist(popmat.orig) * pop.found
    ssd.human <- stable.stage.dist(popmat.orig)
    plot(0:80, ssd.human, type="l", xlab="age (years)", ylab="proportion")
    
    #################
    ## project
    ## set time limit for projection in 1-yr increments
    yr.st <- 1788
    #************************
    #yr.end <- 1861 # set projection end date
    yr.end <- 1901 # set projection end date
    #yr.end <- 1971 # set projection end date
    #************************
    t <- (yr.end - yr.st)
    
    tot.F <- sum(popmat.orig[1,])
    popmat <- popmat.orig
    yr.vec <- seq(yr.st,yr.end)
    
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
    n.mat[,1] <- init.vec
    
    ## set up projection loop
    for (i in 1:t) {
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    yrs <- seq(yr.st, yr.end, 1)
    plot(yrs, (n.pred),type="l",lty=2,pch=19,xlab="year",ylab="N")
    
    # compensatory density feedback
    K.max <- 1*pop.found
    K.vec <- c(1, K.max/2, 0.7*K.max, K.max) 
    red.vec <- c(1,0.9997,0.99881,0.99618)
    plot(K.vec, red.vec,pch=19,type="b")
    Kred.dat <- data.frame(K.vec, red.vec)
    
    # logistic power function a/(1+(x/b)^c)
    param.init <- c(1, K.max, 1)
    fit.lp <- nls(red.vec ~ a/(1+(K.vec/b)^c), 
                  data = Kred.dat,
                  algorithm = "port",
                  start = c(a = param.init[1], b = param.init[2], c = param.init[3]),
                  trace = TRUE,      
                  nls.control(maxiter = 1000, tol = 1e-05, minFactor = 1/1024))
    fit.lp.summ <- summary(fit.lp)
    plot(K.vec, red.vec, pch=19,xlab="N",ylab="reduction factor")
    K.vec.cont <- seq(1,2*pop.found,1)
    pred.lp.fx <- coef(fit.lp)[1]/(1+(K.vec.cont/coef(fit.lp)[2])^coef(fit.lp)[3])
    lines(K.vec.cont, pred.lp.fx, lty=3,lwd=3,col="red")
    
    a.lp <- coef(fit.lp)[1]
    b.lp <- coef(fit.lp)[2]
    c.lp <- coef(fit.lp)[3]
    
    ## compensatory density-feedback deterministic model
    ## set population storage matrices
    n.mat <- matrix(0, nrow=age.max+1, ncol=(t+1))
    n.mat[,1] <- init.vec
    popmat <- popmat.orig
    
    ## set up projection loop
    for (i in 1:t) {
      totN.i <- sum(n.mat[,i])
      pred.red <- as.numeric(a.lp/(1+(totN.i/b.lp)^c.lp))
      diag(popmat[2:stages,]) <- Sx*pred.red
      popmat[stages,stages] <- 0 # Sx[stages-1]
      popmat.orig <- popmat ## save original matrix
      n.mat[,i+1] <- popmat %*% n.mat[,i]
    }
    
    n.pred <- colSums(n.mat)
    plot(yrs, n.pred, type="l",lty=2,pch=19,xlab="year",ylab="N")
    abline(h=pop.found, lty=2, col="red", lwd=2)
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
    m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
    
    for (e in 1:iter) {
      popmat <- popmat.orig
      
      n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
      n.mat[,1] <- init.vec
      
      for (i in 1:t) {
        # stochastic survival values
        s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
        s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
        s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
        
        # stochastic fertilty sampler (gaussian)
        fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
        m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
        
        totN.i <- sum(n.mat[,i], na.rm=T)
        pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
        
        diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
        popmat[age.max+1,age.max+1] <- 0
        popmat[1,] <- m.arr[i,,e]
        n.mat[,i+1] <- popmat %*% n.mat[,i]
        
      } # end i loop
      
      n.sums.mat[e,] <- ((as.vector(colSums(n.mat))/pop.found))
      
      if (e %% itdiv==0) print(e) 
      
    } # end e loop
    
    n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
    n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
    n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
    
    plot(yrs,n.md,type="l", main = "", xlab="year", ylab="pN1", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
    lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
    lines(yrs,n.up,lty=2,col="red",lwd=1.5)
    
    
    ##############################################
    ## invoke mortality directly across n vector
    ##############################################
    
    ## stochatic projection with density feedback
    ## set storage matrices & vectors
    iter <- 1000
    itdiv <- iter/10
    
    # kill (average additional deaths/year)
    #killed.pyr.vec <- seq(1000, 8000, 50) # to 1861
    killed.pyr.vec <- seq(1000, 5000, 50) # to 1901
    
    
    N.md.end <- N.lo.end <- N.up.end <- rep(NA, length(killed.pyr.vec))
    
    for (k in 1:length(killed.pyr.vec)) {
      
      n.sums.mat <- matrix(data=NA, nrow=iter, ncol=(t+1))
      m.arr <- array(data=NA, dim=c(t+1, age.max+1, iter))
      
      for (e in 1:iter) {
        popmat <- popmat.orig
        
        n.mat <- matrix(0, nrow=age.max+1,ncol=(t+1))
        n.mat[,1] <- init.vec
        
        for (i in 1:t) {
          # stochastic survival values
          s.alpha <- estBetaParams(Sx, Sx.sd^2)$alpha
          s.beta <- estBetaParams(Sx, Sx.sd^2)$beta
          s.stoch <- rbeta(length(s.alpha), s.alpha, s.beta)
          
          # stochastic fertilty sampler (gaussian)
          fert.stch <- rnorm(length(popmat[,1]), fert.vec, fert.sd.vec)
          m.arr[i,,e] <- ifelse(fert.stch < 0, 0, fert.stch)
          
          totN.i <- sum(n.mat[,i], na.rm=T)
          pred.red <- a.lp/(1+(totN.i/b.lp)^c.lp)
          
          diag(popmat[2:(age.max+1),]) <- s.stoch*pred.red
          popmat[age.max+1,age.max+1] <- 0
          popmat[1,] <- m.arr[i,,e]
          n.mat[,i+1] <- popmat %*% n.mat[,i]
          
          # extra deaths
          n.mat[,i+1] <- n.mat[,i+1] - (ssd.human * killed.pyr.vec[k])
          
        } # end i loop
        
        n.sums.mat[e,] <- as.vector(colSums(n.mat))
        
        if (e %% itdiv==0) print(e) 
        
      } # end e loop
      
      n.md <- apply(n.sums.mat, MARGIN=2, median, na.rm=T) # mean over all iterations
      n.up <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.975, na.rm=T) # upper over all iterations
      n.lo <- apply(n.sums.mat, MARGIN=2, quantile, probs=0.025, na.rm=T) # lower over all iterations
      
      plot(yrs,n.md,type="l", main = "", xlab="year", ylab="N", lwd=2, ylim=c(0.95*min(n.lo),1.05*max(n.up)))
      lines(yrs,n.lo,lty=2,col="red",lwd=1.5)
      lines(yrs,n.up,lty=2,col="red",lwd=1.5)
      
      N.md.end[k] <- n.md[length(n.md)]
      N.lo.end[k] <- n.lo[length(n.md)]
      N.up.end[k] <- n.up[length(n.md)]
      
      print('________________')
      print(killed.pyr.vec[k])
      print('________________')
      
    } # end k loop
    
    tot.add.deaths <- t*killed.pyr.vec*2
    plot(tot.add.deaths, 2*N.md.end, type="l", main="", xlab="total extra deaths 1788-1861", ylab="N (1861)",
         ylim=c(min(2*N.lo.end), max(2*N.up.end)))
    lines(tot.add.deaths, 2*N.lo.end, lty=2, col="red")
    lines(tot.add.deaths, 2*N.up.end, lty=2, col="red")
    #abline(h = 192845, lty=2, col="red", lwd=2) # to 1861
    #abline(h = 177538, lty=2, col="red", lwd=2) # to 1861
    abline(h = 134171, lty=2, col="red", lwd=2) # to 1901
    abline(h = 92334, lty=2, col="red", lwd=2) # to 1901
    
    # total deaths to 1861
    #tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(177538,192845))))] # to 1861
    #tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(177538,192845))))] # to 1861
    
    # total deaths to 1901
    tdlo <- tot.add.deaths[which.min(abs(N.lo.end - mean(c(134171,92334))))] # to 1901
    tdup <- tot.add.deaths[which.min(abs(N.up.end - mean(c(134171,92334))))] # to 1901
    
    tdmn <- mean(c(tdlo,tdup))
    print(c(tdmn, tdup, tdlo))

    # prop deaths
    print(c(tdmn / (pop.found*2), tdup / (pop.found*2), tdlo / (pop.found*2)))
    
    # average/year
    dpylo <- tdlo / t
    dpyup <- tdup / t
    dpymn <- tdmn / t
    print(c(dpymn, dpyup, dpylo))
    
    # average r to 1861
    #log(mean(c(177538,192845)) / (pop.found*2)) / t
    
    # average r to 1901
    log(mean(c(134171,92334)) / (pop.found*2)) / t
    
    
    
    #####################################################
    ## bootstrapped mean range for modelled/Ne numbers
    #####################################################
    
    Nmd.npp <- 5222387 # NPP model
    Nmd.Zhu <- 1556314 # Australia-wide estimate from Zhu et al. (2021) based on Scenario 2
    Nmd.14C <- 1955000; Nlo.14C <- 1160000; Nup.14C <- 2750000 # Williams et al. 2013
    Nmd.TNe <- 1354000; Nlo.TNe <- 308000; Nup.TNe <- 2400000 # Tobler et al. 2017
    Nmd.MNe <- 2946970; Nlo.MNe <- 22960; Nup.MNe <- 5870980 # Malaspinas et al. 2017
    
    # sd
    Nse.14C <- ((Nmd.14C-Nlo.14C) + (Nup.14C-Nmd.14C))/2/1.96
    Nse.TNe <- ((Nmd.TNe-Nlo.TNe) + (Nup.TNe-Nmd.TNe))/2/1.96
    Nse.MNe <- ((Nmd.MNe-Nlo.MNe) + (Nup.MNe-Nmd.MNe))/2/1.96
    
    NCV.14C <- Nse.14C/Nmd.14C
    NCV.TNe <- Nse.TNe/Nmd.TNe
    NCV.MNe <- Nse.MNe/Nmd.MNe
    
    NCV.mn <- mean(c(NCV.14C,NCV.TNe,NCV.MNe))    
    Nse.npp.calc <- Nmd.npp*NCV.mn
    Nse.Zhu.calc <- Nmd.Zhu*NCV.mn
    
    biter <- 10000
      Nrnd.npp <- round(rtruncnorm(biter, a=0, b=Nmd.npp, mean=Nmd.npp, sd=Nse.npp.calc), 0)
      Nrnd.Zhu <- round(rtruncnorm(biter, a=0, b=Nmd.Zhu, mean=Nmd.Zhu, sd=Nse.Zhu.calc), 0)
      Nrnd.14C <- round(rnorm(biter, mean=Nmd.14C, sd=Nse.14C), 0)
      Nrnd.TNe <- round(rnorm(biter, mean=Nmd.TNe, sd=Nse.TNe), 0)
      Nrnd.MNe <- round(rnorm(biter, mean=Nmd.MNe, sd=Nse.MNe), 0)
      
      #Nrnd.all <- c(Nrnd.npp,Nrnd.Zhu,Nrnd.14C,Nrnd.TNe,Nrnd.MNe) # including Zhu et al. (2021) estimate
      Nrnd.all <- c(Nrnd.npp,Nrnd.Zhu,Nrnd.14C,Nrnd.TNe) # including Zhu et al. (2021) & excluding Malaspinas et al. estimates
      #Nrnd.all <- c(Nrnd.npp,Nrnd.14C,Nrnd.TNe,Nrnd.MNe) # excluding Zhu et al. (2021) estimate
      #Nrnd.all <- c(Nrnd.npp,Nrnd.14C,Nrnd.TNe) # excluding Zhu et al. (2021) and Malaspinas et al. estimates
      Nmn.boot <- median(Nrnd.all, na.rm=T)
      Nsd.boot <- sd(Nrnd.all, na.rm=T)
      Nmn.boot + Nsd.boot
      Nmn.boot - Nsd.boot
      Nlo.boot <- quantile(Nrnd.all, probs=0.125, na.rm=T) # lower 75th %ile
      Nup.boot <- quantile(Nrnd.all, probs=0.875, na.rm=T) # upper 75th %ile
      
      NmedBS <- bootstrap(Nrnd.all, biter, theta=mean)$thetastar
      NmedBS.up <- quantile(NmedBS, probs=0.125, na.rm=T)
      NmedBS.lo <- quantile(NmedBS, probs=0.875, na.rm=T)
      NmedBS.md <- mean(NmedBS)
      print("population range")
      print(c(Nlo.boot, NmedBS.md, Nup.boot))
      
area.aus <- 7688287 # km2
print("density range")
print(c(Nlo.boot/area.aus, NmedBS.md/area.aus, Nup.boot/area.aus))

      
##########################################
# projection to median pre-colonial size
##########################################

census.dat <- data.frame('year'=c(1971,1976,1981,1986,1991,1996,2001,2006,2011,2016,2021),
                         'N'=c(115953,160912,159897,227645,265459,352970,410003,455028,548368,649171,812728))
len.census.dat <- dim(census.dat)[1]
census.r <- log(census.dat$N[2:len.census.dat]/census.dat$N[1:(len.census.dat-1)]) / diff(census.dat$year)
census.r.mn <- mean(census.r)
census.r.mn
years.ahead <- seq(1,30)
N.proj <- round(census.dat$N[len.census.dat]*exp(census.r.mn*years.ahead), 0)
years.fut <- 2021+years.ahead
plot(years.fut, N.proj, type="l")
abline(h=2220000, lty=2, col="red")
target.N <- years.fut[which.min(abs(N.proj - 2210000))]
target.N
abline(v=target.N, lty=2, col="red")
