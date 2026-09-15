"""Graphics-only orthographic projection; never used to decide geometric validity."""
import math

def project(point,center,span,angle,elevation,width=1920,height=1080):
    delta=[p-c for p,c in zip(point,center)]
    right=(-math.sin(angle),math.cos(angle),0)
    up=(-math.cos(angle)*math.sin(elevation),-math.sin(angle)*math.sin(elevation),math.cos(elevation))
    return (width/2+width/span*sum(a*b for a,b in zip(delta,right)),
            height/2-width/span*sum(a*b for a,b in zip(delta,up)))
